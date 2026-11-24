# pequalnp-pilot-47: L-meta-4340

Sole lease held by root; assigned 2026-11-24T23:11:05Z. Exact desk response and statement in job scratch. No other gap work permitted.

Strategies: root (finite lower-bound/reduction integration), structural_proof (direct proof), counterexample (witness search), reduction (useful cut), status_review (checker/review), lean_setup (toolchain).

Append concise UTC-tagged findings below.

2026-11-24T23:13:37.335960+00:00 counterexample strategy: definitions verified. Missing wire reads false. NOT can negate an original input despite leaf restriction by `.not [i,9]` (second input ignored). Exhaustive 4096 edge orientations: star-cover cost with free OR is 16 for (0,1),(0,4),(4,6), and 15 for (0,2),(0,3),(0,6). These are restricted-model computations, not general lower bounds. C++ stochastic 14-gate search started, all 512 truth-table rows evaluated; closest found so far differs on 5 rows. Logs and source in /tmp/oec/pequalnp-pilot-47/counterexample/.

### 2026-11-24T23:13:38.515899+00:00 structural_proof
Circuit semantics: forward/out-of-range wire reads are false; NOT only reads first input. FanInTwo permits empty/singleton gates and NOT with a second dummy input. Original restriction only forbids AND/NOT when ALL syntactic input indices are <9, so NOT [i,9] remains permitted.
Existing complete OR first-gate lower bounds: L_meta_1673.final for (0,1), L_meta_1674.bound for (0,2), L_meta_1676.finish for (0,4), and embedded L_meta_4962.bound for (4,6) with no second-gate assumptions. Last file is 336702 bytes; many related child proofs copy the same full bound. OR (0,3): L_meta_3594.bound_not1 handles any NOT in tail; L_meta_4463.FullBound.bound handles Monotone2. OR (0,6): no full bound found; L_meta_3610 only excludes tails <=13, L_meta_3248 and L_meta_4702 prove a 13 non-NOT gate cofactor lower bound.
Allowed project imports only PEqualNP.Defs; outside helpers cannot directly be used. Full proof by copying six case developments faces 512KiB limit and missing OR06 case. Checked reduction R_meta_1677_361 splits OR06 into binary lower bound and at-most-one-NOT optimum; binary lower bound appears available as L_meta_3248.cofactor3248.

Reduction agent: 2026-11-24T23:14:10.431916+00:00 min-wire24 canonicalization: 2000 random legal circuits of size0..14; 20000 evaluations on length10 Boolean inputs; equality and direct-gate condition all pass. This is a computational sanity check, not Lean validation.

2026-11-24T23:15:27.913702+00:00 status_review: L-meta-1035 public record remains conjecture, seat=null, attempts=[] at data.pequalnp.com/data/lemma/L-meta-1035.14ea345977c1.json; complete 2136-open-PR census has no matching target. Independent min24 normalization check passed 204800 comparisons (200 deterministic random circuits, every ten-bit input) and preserved special direct-gate restriction; size0..14, arity0..2, AND/OR/NOT, index/output0..50, forward references covered. Bounded normalization gives genuinely finite search. Guard/checker review: reduce requires 2..4 independent closed propositions, exact structural conclusion, no helpers, children <=2000 printed chars, no exact parent subterm. Run outside-guard imports with explicit reduce kind as well as check-lean reduce.

Reduction agent: 2026-11-24T23:15:40.058472+00:00 exact-arity2 canonicalization: 2000 random legal circuits of size0..14; 20000 evaluations on length10 Boolean inputs; equality, exactly2 inputs per gate, and direct-gate condition all pass. NOT binary second input retained. Computational sanity check only.

2026-11-24T23:19:40.071186+00:00 Reduction agent: both basic clamp and exact-arity2 variants compile using lake env lean. Stronger exact2 version has two finite lower-bound children (five known OR pairs and remaining OR06), 127 source lines; log /tmp/oec/pequalnp-pilot-47/reduction/exact-build-002.log. Root informed immediately for push-early preservation. Separate topological exact2 variant now compiling; it will eliminate forward references by mapping each to sentinel24.

2026-11-24T23:19:54.373419+00:00 counterexample strategy: TightUpper.lean successfully compiled (exit0), proving a 15-gate AND/OR tail for supplied OR(0,6), FanInTwo, direct-gate restriction, and all512-input correctness by kernel evaluation. It is a tight upper bound component, not proof/refutation of gap4340. Full successful Lean log is empty, scratch counterexample/tight-upper-lean.log. Three 300-second stochastic14-gate searches found no witness after1,174,300,000 /1,228,150,000 /1,190,750,000 mutation attempts (pairs02/03/06), minimum3 errors each; not exhaustive.

2026-11-24T23:20:17.617538+00:00 Reduction agent: stronger topological normalizer compiled. In each gate i, both pins are earlier wires <10+i or sentinel24; all gates have exactly2 pins. Circuit size and semantics preserved. Two finite children split known five pairs vs remaining OR06. 150lines; source /tmp/oec/pequalnp-pilot-47/reduction/R_meta_4340_47_topo.lean, log topo-build-002.log. Root notified for immediate preservation; file frozen.

Reduction agent: 2026-11-24T23:20:34.462204+00:00 topological exact-arity2 canonicalization: 2000 random legal circuits, 20000 Boolean-input evaluations. Evaluation equality, direct restriction, exact2 pins and each pin<10+i or=24 all pass. Computational sanity check supplements Lean compile, not a proof of either finite lower-bound child.

2026-11-24T23:20:38.943347+00:00 counterexample strategy complete: pair06 exactly-one-NOT search finished1,257,620,000 mutation attempts, best6 erroneous rows; requiring the NOT wire in the output dependency cone finished1,152,620,000 attempts, best10 erroneous rows. No counterexample. Searches omit explicit missing-wire constants, so neither exhaustive nor a complete basis census. One checked component delivered: TightUpper.lean (34 lines,1193 bytes), Lean exit0; source and validation file in scratch counterexample/.

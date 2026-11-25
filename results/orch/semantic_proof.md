# Semantic lower-bound investigation

- 2026-11-25 14:04 UTC: circuit semantics checked; no loophole found. FanInTwo restricts gate operations and fanin, out-of-range wires read false.
- Existing checked L_meta_4725 gives 15 + notCount C <= C.size for Petersen, independently of number of NOT gates. Copied helpers under assigned namespace in lemmas/Semantic.lean and added five_not_excluded, ruling out five or more NOT gates within 19 total gates. Awaiting root toolchain/cache readiness to compile.
- Remaining hard cases have 1, 2, 3, or 4 NOT gates. Shared with combinatorial_bound agent, who investigates restrictions and 9-vertex induced graph bounds.
- L_meta_2453/2455/2457 concern a 10-vertex theta subgraph, not the full Petersen graph.

- 2026-11-25T14:05:23.269361+00:00: Compact last-NOT decomposition drafted in lemmas/CutLast.lean (87 lines), including zero-input and invalid-input NOT semantics. Awaiting compilation.

- 2026-11-25T14:08:45.955474+00:00: `lake env lean results/orch/lemmas/CutLast.lean` completed with exit 0 and empty stdout/stderr. Final compact source: 86 lines. Root and independent reviewer notified for early push.

- 2026-11-25T14:22:29.356584+00:00: SignedRestrictionPlain.lean compiled (1785 lines), using products instead of custom structures and explicit proof-local decidability. ReachBridge.lean compiled against the exact generic Reach interface from L_meta_5236. Generic false-cofactor floor consumer is compiling; toolchain agent will instantiate its model with the finite signed certificate.

- 2026-11-25T14:25:45.044652+00:00: CofactorFloor.lean compiled with exit 0 and empty stdout/stderr in CofactorFloorTest.lean. It transports a row-model lower bound through checked Petersen inverse automorphisms to every false cofactor. Toolchain agent has separately checked the concrete finite model assumptions; few_nots agent can discharge ZeroFloor15 after integration. All checked source fragments are now frozen.

- 2026-11-25T14:33:28.483696+00:00: Assembled BinarySeventeen.lean (6870 lines, 396474 bytes) from all checked components. Independent static review passed. The 17-binary lower-bound suffix passed a lightweight exact-interface test; full kernel build is running with stdout/stderr saved as binary-seventeen.* and .olean emission enabled. No errors observed so far. Final corollaries exclude at least three NOT gates and force the remaining bounded circuit to contain exactly one or two NOT gates.

- 2026-11-25T14:40:45.126692+00:00: Full BinarySeventeen.lean kernel build completed with exit0; no errors and empty stderr. Stdout contains inherited linter/deprecation warnings. The frozen 6870-line, 396474-byte artifact proves 17 + notCount C <= C.size and excludes at least three NOT gates. Root notified immediately to preserve/push. Emitted BinarySeventeen.olean will validate subsequent suffixes without rebuilding the finite certificate.

- 2026-11-25T14:41:35.411717+00:00: ConcreteFirstCases.lean compiled against emitted BinarySeventeen.olean (exit0, empty output), proving unconditional first-source sign rigidity and exact two-NOT saturation via BinarySeventeenCasesSuffix.lean. OverlapTest.lean also compiled (exit0, empty output), proving that no later consumer of the first signed gate can simultaneously read either first input. The replacement preserves minimum size and creates a forbidden positive occurrence of the other first input. Both suffixes are frozen; root and independent reviewer notified, and the counterexample agent's matching SAT constraint is now justified.

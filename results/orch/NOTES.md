# L-meta-2592

Exact assignment: /tmp/oec/pequalnp-pilot-101/desk-first.json
Statement: /tmp/oec/pequalnp-pilot-101/statement.txt
At least one NOT (possibly unused or multiple), at most 19 gates, Petersen graph. Allowed project module: PEqualNP.Defs only. Three live reductions already exist. All strategies append their findings here and use distinct files under results/orch/lemmas/. Only root holds lease, builds final, commits and pushes.

## Counterexample search initial
Exact brute combinatorics: Petersen minimum vertex cover 6; 5 covers, yielding 40 oriented-star 20-gate seeds. Function false on 76/1024 assignments. No semantic shortcut from invalid wire indices. Preparing truth-table local optimization to find 19 gates with NOT.

## Semantic audit (2026-11-25T13:52:27.552308+00:00)
- The posted assumption is at least one NOT anywhere, not exactly one; unused NOT gates count.
- FanInTwo restricts the gate operations to AND/OR/NOT and each argument list to length at most two. NOT ignores its second argument. Forward or missing references read false. Empty AND/NOT gates give true, at gate cost. No semantic loophole was found.
- The 15 edges in the statement match Petersen. The Boolean precedence is ordinary AND before OR.
- The naive dependency bound would only give at least nine non-NOT gates; the existing L_meta_4725 is strictly stronger and should be reused by inlining. Its proof normalizes with a non-NOT budget then minimizes total gates. Its branch-count inequality is branches.card + n + gates.length - 1 + notGateCount <= 2*gates.length. It derives six branch wires, hence 15 non-NOT gates for n=10.
- To exploit equality at 15 non-NOT gates, one must establish additional branch/read constraints. The existing theorem does not retain the original NOT count in the chosen least circuit: least_with_budget minimizes among circuits with nonNotCount <= original, and can change NOT count. Thus one cannot directly infer an equality-case normal form with exactly four NOTs from that minimizer. A total-size-and-NOT-budget preserving minimizer would need separate proof.
- R_meta_4727_53 reduces the remaining 1–4 NOT case to a signed BinaryCircuit lower bound. It compiles NOTs into polarity marks N, with N.card <= notCount and D.size + notCount <= original.size. SignedBound is still the mathematical hard part.

## Existing reductions strategy

- `R_meta_2592_271`: binary floor + circuits with 1–4 NOT gates. Binary floor is already checked in `L_meta_4725.lean` (3224 lines, 146284 bytes): `15 + NotBracket.notCount C ≤ C.size`. Its first-boundary/twin-group argument proves six branch wires. This rules out at least five NOTs under the 19-gate budget.
- `R_meta_2592_318`: last-NOT decomposition + separator. Decomposition already checked exactly as `L_meta_8295.lean` (66 lines). Remaining separator has prefix allowed arbitrary NOTs and monotone suffix.
- `R_meta_2592_408`: normalize invalid reads and trim output, then normalized lower bound.
- 1–4 NOT child is `L-meta-4727` (file absent, still unresolved). Its three reductions are R4727_1 (trivial case split; child L8021 only contradictory no-NOT case), R4727_17 (semantic signed compilation + lower bound), R4727_53 (binary signed compilation + lower bound). Both compilers already checked: `L_meta_6060.lean` and `L_meta_7227.lean`, respectively.
- Five first-gate orbits in parent `R_meta_651_1`: unary/constant, AND adjacent, OR adjacent, OR nonadjacent, AND nonadjacent. Unresolved parent first-gate children include L1888/L1890 (no main files). For OR nonadjacent (extra x0||x2), checked L5236 rules out 3–4 NOTs and checked L5238 rules out at least five; 0 and 1–2 NOT branches remain unresolved.

## Lower-bound strategy (13:58 UTC)

The generic first-branch-group theorem in L_meta_4725 gives 15 binary gates for Petersen, from n-1 plus six twin-removal groups. This does not presently strengthen to 19. A new standalone partial is at results/orch/lemmas/LowerBound.lean: normalized effective reads count NOT as unary; if every input has two reads and each nonoutput gate has one read, a NOT-containing ten-input circuit needs at least20 gates. It is not yet compiled (cache setup ongoing). Therefore a hypothetical size19 circuit must have a single-use primary input after normalization. For a single-use primary input v, merging it directly with another primary input u via AND/OR cannot compute Petersen: AND loses v-neighbor witnesses not equal u; OR loses witnesses distinguishing the unequal neighborhoods of v and u. The hard case is v first meeting an already-computed wire.

Read notes/note-1-edge-function-exact-size.md: |E|+tau-1 is proved only for forests/cycles/long-thread graphs; Petersen does not meet the long-thread hypotheses. Web search did not provide a usable generic NOT elimination theorem.

## Environment setup (2026-11-25 13:52:50 UTC)

No accessible prepared Lean or Mathlib cache existed. Downloaded official Lean 4.36.0 Linux release to scratch; verified version and pinned dependency manifest. `lake exe cache get` exited 0 and decompressed 9117 artifacts; full Mathlib.olean is present. No Mathlib source build and no lake update.

Command prefix for builds/checker: `PEQUALNP_REAL_LAKE=/tmp/oec/pequalnp-pilot-101/toolchain/lean-4.36.0-linux/bin/lake PEQUALNP_HOME=/tmp/oec/pequalnp-pilot-101/build-queue XDG_CACHE_HOME=/tmp/oec/pequalnp-pilot-101/cache PATH="/workspace/pequalnp-proofs/tools/bin:/tmp/oec/pequalnp-pilot-101/toolchain/lean-4.36.0-linux/bin:$PATH"`. Bundled SAT solver: `/tmp/oec/pequalnp-pilot-101/toolchain/lean-4.36.0-linux/bin/cadical`. Full logs are scratch files `toolchain-download.*`, `toolchain-extract.*`, `cache-help.*`, `cache-get.*`.

Reviewer reminder: the posted statement assumes at least one NOT anywhere in the gate list, not exactly one; multiple NOT and unreachable/dead NOT gates must be covered.

## Few-negations strategy 2026-11-25T13:53:46.412270+00:00

Checked partial `lemmas/FewNegations.lean`: both constant-replacement criteria compile. If the two replacements Q(x,false) and Q(x,true) are monotone in x, Q is monotone in its final bit, and Q(x,!H(x))=F(x), then (a) if every true x has a smaller true certificate y with H(y)=true, replacement false computes F; (b) if every false x has a larger false certificate y with H(y)=false, replacement true computes F. Applied to graph functions, H true on every edge input suffices for (a), H false on every maximal independent-set input suffices for (b). An essential NOT must violate both conditions. A single final AND after nonconstant monotone H fails at all-true; single final OR fails at all-false. Need further gate accounting to reach 20; no full proof yet.

## Counterexample search SAT audit
The 30-row necessary constraints (15edges+15maximal independent sets) are too weak with NOT: first-NOT SAT model has6NOT and682 wrong rows of1024; first-AND-edge and first-OR-nonedge also SAT but fail full truth-table validation. These are not counterexamples. Strengthened187-row CEGAR with1–4NOT underway in coordination with semantic_audit. Stochastic full truth-table search best current19gate approximation has9 errors and0NOT, hence also no counterexample.

## Focused hexagon construction ruled out computationally
Deleting vertex0 and neighbors1,4,5 leaves C6 on order[2,3,8,6,9,7]. Let H be its edge function and U=x2∨x6, V=x3∨x9, W=x7∨x8. Petersen f = H∨x1(U∨x0)∨x4(V∨x0)∨x5(W∨x0). Thus a10gate circuit exposing H,U,V,W would yield19 gates overall. SAT with U,V,W fixed as first3OR gates and H last, all64rows, nonconstant positive source wires, all remaining gates live: UNSAT with exactly1NOT (6.52s), and UNSAT with1–7NOT (10.67s). This is a restricted computational exclusion, not a Lean-checked lower bound or full-gap proof. Script search_hexagon.py; full artifacts scratch/counterexample/hexagon10*.

## SAT audit and CEGAR 2026-11-25T13:59:37.628224+00:00
- Minimal 30-row NOT-first SAT model is not a counterexample: independent decoder agrees on all 30 encoded rows but fails 682 of 1024 full truth assignments.
- Added unique structural selectors and at most 4 NOTs from checked binary floor. Batch NOT-first 187-row run returned UNKNOWN after 240 seconds; OR-nonedge 192-row and AND-edge 192-row runs ongoing. These constrain a full 19-gate nonpadding normal form, so no lower-bound completeness claim.
- Incremental native driver links bundled libcadical.a and libc++ archives through verified C API, freezes selectors, validates all 1024 rows, adds 16 bad rows per SAT candidate, and retains learned clauses. General first-NOT and specialized exactly-1-NOT variants running; latter includes 38 cofactor boundary rows from few_negations.
- Files: sat_validate.py, sat_cegar.py, sat_incremental.cpp under results/orch/lemmas. Full logs/models/CNFs in /tmp/oec/pequalnp-pilot-101/sat-*.

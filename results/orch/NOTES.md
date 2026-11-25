# L-meta-8032 shared notes

Lease assigned 2026-11-25T10:54:34Z. Root alone renews/submits.

Exact statement in /tmp/oec/pequalnp-pilot-83/statement.txt and desk-007.json.

Target: lean/PEqualNP/Outside/L_meta_8032.lean; only allowed project module PEqualNP.Defs.

Root owns target file. Agents use distinct scratch/lemma files and append findings here.

Recorded 2026-11-25T10:56:33.795376+00:00

## Review agent findings
- Local reusable exact semantics bridge: `lean/PEqualNP/Outside/L_meta_8029.lean` (84 lines, imports Defs only) proves that the exact 16 positive pairs and 24 negative masks determine the full graph function for every Monotone2 circuit. Copy helpers into the target namespace; importing the Outside file is forbidden. `L_meta_8231.lean` gives the packed-40-row version.
- Important semantic traps: posted finite encoding allows forward references (read false), empty AND (true), empty OR (false), and unary gates. It does not assume ReadsBack, IsAO2, leastness, output liveness, or TopForm. Junk counts every gate, including unused gates. A normalization that minimizes size can decrease junk and lose the >=3 hypothesis.
- `L_meta_1499` / `L_meta_1501` preserve junk cardinality when converting an already least AO circuit to TopForm. They do not solve the arbitrary-to-least preservation issue.
- General budget `edgeCount + noncentrelessTops + 2*centreless + junk + extraOr <= size + Ustar + 1` is in `L_meta_7862` / `L_meta_1491`, subject to leastness and TopForm. Existing `L_meta_8033`, `8037`, `8039` concern a different 9-vertex Petersen graph.
- `R_meta_8031_401` reduces the positive existence claim to a bit-table search witness and general replay. `R_meta_8031_571` proposes 14-gate/6-gate subcircuits joined with one OR, with 2/1 dirty AND gates respectively. Its hypotheses are unproved; neither reduction supplies a circuit.

## Toolchain/count route (toolchain_setup, 2026-11-25T10:57Z)

PEqualNP.Defs base build passed. Full logs in /tmp/oec/pequalnp-pilot-83/defs-build.stdout and .stderr. All proof agents can use installed pinned toolchain/cache.

Finite graph facts checked by exhaustive Python (not yet Lean): given 24 negatives exactly maximal independent sets; independence number 4, vertex-cover number 7; no C4. Ordinary cover upper bound is 16+7-1=22. General ≥22 circuit size would settle goal even without junk but appears harder than the posted junk≥3 slice. Monotonicity semantic helper source: L_meta_907.lean lines 8–140; shorter eval_mono in L_meta_1521.lean and L_meta_1639.lean.

## Structural findings 2026-11-25T10:57:21.495940+00:00

- Exact-test→full edge-function computation partial compiled at results/orch/lemmas/Structural.lean (81 lines), copied/re-namespaced from checked L_meta_8029. Only Defs import. Logs structural-build.stdout/stderr, exit0.
- Dirty gate count is not direct overhead: checked L_meta_9035 gives six-gate right-piece witness for R_meta_8031_571 with one dirty AND. Expression (x6∨x7) ∧ (x3∨((x6∨x9)∧(x7∨x10))) computes the right five-edge graph. Three ORs, one dirty AND, OR, clean AND.
- R_meta_8031_571 reduces positive search to left14dirty2 and right6dirty1; right piece is checked, left remains potentially useful constructive route.

## Petersen-nine restriction route (toolchain_setup, 2026-11-25T11:01Z)

All 55 two-vertex deletions checked in Python; none matches Petersen-nine degree/triangle signature. Only deleting degree-2 pairs preserves 12 edges, and the only pair removing both triangles is {1,3}; its remaining degree sequence contains degree 4. A monotone variable projection to a loopless triangle-free quadratic target cannot identify two triangle vertices (would create a singleton), so it must set one vertex of each triangle false. Because target has nine essential variables, exactly two vertices can be deleted and no further identifications are possible. Thus direct projection to the nine-variable lower bounds L_meta_8033/8037/8039 is unavailable. More general logical substitutions could evade this but need a nontrivial cost argument.

2026-11-25T10:57:58.169859+00:00: Independent review of Structural.lean: PASS FOR PARTIAL BACKUP PUSH ONLY. Exact edge and negative lists checked programmatically against statement.txt (16 and 24 matches). Only Defs import, own namespace, allowed heartbeat option, no forbidden markers. Helpers establish exact graph-test semantics; no final theorem yet, hence not PR-ready. Right-six-gate diagnostic dropped because root reports L_meta_9035 already resolves it.

## Counterexample strategy (10:58 UTC)

The24 false masks are exactly all maximal independent sets (125 independentsets total, independence number4). AND/OR circuits remain monotone with missing/forwardrefs(defaultfalse), so thereis no semantic loophole: the40tests force thefullgraphfunction.

SAT synthesis rightcomponent6gates+1junk succeeds: `11=6∨7;12=6∨9;13=7∨10;14=12∧13;15=3∨14;16=11∧15`. Root reports thiscomponent alreadyLeanchecked inL_meta_9035. Leftcomponent has8vertices11edgescover5; left14+2junk SAT running. Filesandencoding in `/tmp/oec/pequalnp-pilot-83/counterexample/`.

## Finite-search route (2026-11-25T10:59:08.354906+00:00)

- Generic certificate bridge compiled: `results/orch/lemmas/FiniteSearch.lean`,161lines, `L_meta_8032_aux.packed_search_sound`. Exact40-row packed search certificate gives positive twin with3dirty witnesses, replay proven inline. Root notified immediately for earlypush.
- Public LRAT verified enc/enc2 includes normalization which may remove dirtygates; useful only for stronger entire21gate lowerbound, unless dirty preservation separately established.
- Direct Python mirror generated enc21(67,083 clauses) and enc2_21(207,518clauses). Bounded60sCaDiCaL probe gave noSAT/UNSAT answer; full logs in scratchfinite_search.
- Childsat_encode probes raw21gate model with3dirty, while counterexampleagent searches left14/right6 construction.

## SAT encoding status 2026-11-25T10:59:26.474931+00:00

sat_encode generated a 21-gate, 40-row, AO circuit CNF (3625 variables, 81000 clauses) with constants and arbitrary output, plus 3 distinct dirty-AND witnesses. The initial 60-second CaDiCaL run was UNKNOWN (896541 conflicts); no proof or counterexample. Files are /tmp/oec/pequalnp-pilot-83/finite_search/sat/. A second restricted encoding assumes live, binary nonconstant gates and final output; this is witness search only, not a complete lower-bound reduction.

2026-11-25T10:59:36.078545+00:00: Independent review of FiniteSearch.lean: PASS FOR COMPILED PARTIAL BACKUP PUSH. Its packed_search_sound conclusion exactly matches the positive existential negated by assigned statement (whitespace-normalized automated comparison). Recomputed packed columns independently; all eleven match, and all twenty-four negative masks are independent. Injective three-gate witness yields three distinct dirty AND gates. This is a sufficient certificate for backward binary circuits only, not a completeness reduction for optional/forward wires. Two own namespace blocks M and M_aux are allowed by current guard. No forbidden markers, only Defs import and scoped allowed limits.

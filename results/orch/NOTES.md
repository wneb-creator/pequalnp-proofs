# L-meta-2592 orchestration notes

Goal: no fan-in-two circuit of size at most 19 containing a NOT computes the Petersen edge function.
Only root holds/renews lease. No agent desk calls or git mutations.
Desk snapshot: /tmp/oec/pequalnp-pilot-120/desk-001.json
Current reductions_live=3 (capacity full). Allowed project module: PEqualNP.Defs.
Agents append timestamped findings here and use distinct files in results/orch/lemmas; no edits to final proof file.
Parent owns build/cache preparation. Read CONTRIBUTING.md and README.md first.

## 2026-11-25T14:17:56.484030+00:00 finite_certificate
General NOT CNF bridge exists: Library/LRAT/LinkN.lean and LinkN2.lean lower_of_unsat2. They are not reachable from allowed Defs import; inlining needs their checker + Shannon prerequisites and several structures (manual-review path). Defs/LratEncoding covers monotone circuits only. notes/data/lrat-link/gennot.py generates a matching AND/OR/NOT formula. Direct finite enumeration after capping wire IDs has roughly 10^67 syntactic circuit codes at s=19, so raw decide is infeasible.
Created results/orch/lemmas/finite_certificate_normalize.lean: cap all indices at n+s, retain exact size, all operations including NOT, fan-in, and input semantics; awaiting root toolchain setup for Lean test. This is a useful finite normalization partial with no structures or new axioms.

2026-11-25T14:17:58.229667+00:00: circuit_search: exact 1024-row bit-parallel local optimization running for 20 min. Best found 19-gate monotone circuit has 9 mismatches; independently Python-checked. This is only a near miss, not a refutation or lower-bound certificate. SAT tool unavailable on PATH; seeking bundled Lean cadical.

2026-11-25T14:18:44.321583+00:00: circuit_search exact SAT started: gennot.py full1024 rows,19 gates,1–3 NOT, 211000 vars/1433321 clauses. Canonical firstgate NOT0 and AND01 running1200s each; AND02/OR01/OR02 generated. Source cardinality/case additions mirror obvious clauses; no UNSAT claim yet.

2026-11-25T14:18:44.804946+00:00: not_elimination: NotPremium/NotBracket offer definitions, not a general elimination theorem. Broad constant-replacement argument is false (f=y via (x AND y) OR ((NOT x) AND (x OR y))). Drafted monotone-prefix/final-NOT antitonicity partial in results/orch/lemmas/not_elimination_last.lean, awaiting toolchain to check.

## 2026-11-25T14:19:24.754493+00:00 status_review audit
- No semantic loophole found: forward and absent wire reads are false; constants are counted; extra NOT operand is ignored.
- R2592_271 binary floor child is checked as L_meta_4725 (3224 lines); stronger L_meta_6581 (4555 lines) gives 16 non-NOT gates for full Petersen, leaving only 1–3 NOTs under size 19.
- R2592_408 normalization child is checked as L_meta_7389 (305 lines). R2592_318 cutLast child proof is in PR 11694 body; Petersen separator remains open.
- Audited 368 files mentioning Fin 10/PetersenTen; 67 final statements retained in /tmp/oec/pequalnp-pilot-120/status-ten-statements.json. No checked full Petersen binary bound above 16 or complete one-NOT case located. L_meta_9818 gives 17 total gates for Petersen minus two incident edges, using 16-gate Petersen-minus-vertex bound.
- L_meta_8762 and L_meta_8764 (26000 bytes each) supply strong 0-cofactor elimination: remove direct readers and readers of AND/NOT gates driven by the pinned input. L_meta_7774 supplies deletion of any three gates semantically equal to earlier wires on a zero cofactor. These could support a structural gate-elimination route.
- All 15 GitHub 2592 search hits reviewed. Recent PRs 12707,12799,15013 were reductions refused recording due contributor limit, not missing full proofs. Three admitted cuts still require hard children.

## 2026-11-25T14:20:35.001520+00:00 status_review independent partial review
- Reviewed all 103 lines finite_certificate_normalize.lean: mathematically sound clamping to global upper bound n+s, preserves gate size/op/NOT presence/evaluation, namespace and forbidden-text checks clean. PASS as partial helper artifact, contingent on root compilation; no final posted theorem yet, so not a submission proof.
- Precise floor distinction: L9818 Core.monoRoot excludes 15 binary gates without signs; Core.signedRoot excludes 14 binary gates with free signs. Its nine-variable lower bound 16 is TOTAL gates, not 16 binary gates. Existing L6581 already uses signed floor 15 to obtain full Petersen binary floor 16. A stronger signed floor 16 would need a new certificate.

2026-11-25T14:20:51.007948+00:00 gate_lower_bound: Reviewed generic branching and restriction machinery. L_meta_6581 internal nineFloor gives 15 non-NOT gates on Petersen-minus-vertex; full atLeastSixteen projects x0=0 and charges its constant input. L_meta_9818 core gives ordinary size >=16 (not a 16 non-NOT bound), so cannot directly upgrade the binary floor. Next possible subcase: first effective AND/difference gate with a positive primary input, zero that input; the produced wire is constant and its next effective consumer also disappears, yielding >=17 binary. Positive OR first gate remains.

2026-11-25T14:21:44.325000+00:00: not_elimination: input-negation route also stalled. Cofactor pairs (a,b) under xi=0,1 give xi=(0,1), NOTxi=(1,0); target a<=b. Projection (a,b)->(a,a OR b) preserves OR but not AND, so sharing defeats an immediate cost-preserving conversion. A syntactic mux (NOTxi AND A) OR (xi AND B), A<=B, does simplify to A OR (xi AND B), but obtaining mux form can duplicate subcircuits. Do not use the unproved general elimination claim.

2026-11-25T14:24:12.457956+00:00: circuit_search switched AND01 full-table solve to UNKNOWN by interruption to try boundary-row CEGIS; NOT0 full-table remains. CEGIS initial 42 rows, any first gate,1–3 NOTs,180s per solve. Known20 star-cover sanity checked all1024 truth rows and all emitted CNF clauses. Exact logs retained under task tmp.

## 2026-11-25T14:25:28.014162+00:00 status_review partial push audit
- PASS finite_certificate_projection_core.lean (73 lines, compiled with warnings only): all low-half projection identities checked, exact source first constant matches, no forbidden terms or added axioms. Scratch imports Lean and retains L6581 namespace; branch artifact only, not final eligible theorem.
- PASS semantic review finite_certificate_normalize.lean (171 lines): extended finite code/exclusion transfer covers all bounded fan-in-two circuits. PASS not_elimination_last.lean (87 lines): monotone-prefix/final-NOT antitonicity. Compilation of these pending root.
- PASS semantic review new tail gate_lower_bound_first.lean: complete diff vs L6581 confirms unchanged source core except namespace, and first AND with three NOTs would need at least20 gates. This remains a partial exclusion, not full gap. Compilation pending. Full comparison diff /tmp/oec/pequalnp-pilot-120/status-first-diff.txt.

## 2026-11-25T14:25:33.545646+00:00 checker_storage
Unmodified checker requires full Mathlib. Lean4.36 Environment.lean lines2443–2456 eagerly reads .olean, .olean.server, .olean.private for every module; importModules defaults to private and loads IR too. Do not omit private/server files or fake a Mathlib root. Full8712-module Mathlib estimate from2189 cached modules is ~5.6GiB olean/private/server plus~0.4GiB IR; current disk8GiB cannot hold this plus3.1GiB toolchain. Removing only cache tarballs/generated C/IDE data saves<0.5GiB. FUSE mount test under task tmp failed Operation not permitted; no bypass attempted. Possible storage-only alternative, not implemented: sealed memfd backing for2–3GiB of authentic private artifacts, symlinked from build paths to keeper process FDs. Cgroup RAM8GiB/no swap, so pause heavy searches and monitor if attempted. No artifact or toolchain semantics changed.

2026-11-25T14:26:49.311399+00:00: circuit_search: initial42-row CEGIS any-first/1–3NOT timed out at180s with UNKNOWN and no candidate. Switched to first OR(0,2), exactly3NOT,300s per solve. Full-table NOT0 still active. Known20 sanity passed1024 inputs and1424364 CNF clauses; no checked lower bound inferred from search.

2026-11-25T14:27:28.153027+00:00: not_elimination_last.lean compiles with pinned Lean (exit0); full log /tmp/oec/pequalnp-pilot-120/not_elimination_last.log. Exhaustive semantic DAG enumeration on four variables, through six binary AND/OR gates, found 164 nonconstant monotone outputs both with and without free NOT x0, with identical minimum binary costs. This is computational evidence only, not a Lean theorem.

## 2026-11-25T14:28:01.402492+00:00 finite_certificate compiled
finite_certificate_normalize.lean compiled pinnedLean4.36 via lake env lean, exit0, no warnings. 182lines: cap wire indices preserves exact size, fan-in, NOT existence and semantics; finite GateCode/CircuitCode representation; finite exclusion implies original universal circuit exclusion. File frozen for review/checkpoint. Core projection artifact also compiled and renamed to current gap namespace.
Duplicate projected roots cannot be charged like constants. Correct counterexample in signedbasis: mux(a,b,c)=(a AND b) OR ((NOT a) AND c), minimum3 binarygates (exhaustively checked≤2), Run3 from[a,a,b,c]. Petersen OR firstgate retains both rawinputs, but pinningone0 onlychargesoneconstant; AND firstgate with retainedinputcharges2constants.

2026-11-25T14:28:29.026502+00:00: not_elimination: extended semantic DAG enumeration to five variables and <=5 binary gates, yielding 1727 monotone targets with exactly the same minimum binary costs with/without free NOT x0. No counterexample. Low-collapse case analysis remains open: a mixed-sign hazard can occur in a noncollapsing gate, e.g. (xA OR r) AND ((NOT x)B OR s), so direct readers alone do not determine cancellation cost.

## 2026-11-25T14:29:07.107657+00:00 status_review checked finite certificates
- status_review_or_witness.lean compiled pinned Lean exit0, empty log. OR witness low rows [16,128,48,272,64,16,20,65,72,18], high=low+512: target changes, old sources stable except first, new OR source stable or projectszero; projection equals pin_j projection.
- status_review_automorphisms.lean compiled pinned Lean exit0, empty log. For each a in Fin10, explicit permutation maps a to0, preserves Petersen adjacency, and is injective. JSON holds maps and Extended rowweights [512,128,32,256,64,16,4,1,8,2]. Gateagent has both artifacts.
- Both are small importLean scratch certificates, require independent review before root partialpush, and make no fullgapclaim.

2026-11-25T14:30:18.024832+00:00 gate_lower_bound: NEW Lean-checked partial gate_lower_bound_retention_core.lean (158 lines, 11730 bytes), exit0 empty log. For each of four signed binary op choices on input0 and anydistinctinputj, an exact Petersen Live suffix using that produced wire must also retain rawinput0. Concrete1024row witnesses checkedbykernel. This feeds globalbinary17 proof afterinputsymmetry and nineFloor15 projection. Fullcertificate prototype gate_lower_bound_first.lean stillcompiling, noerrorssofar.

2026-11-25T14:34:15.000767+00:00 root replan: broad cost-free NOT elimination remains unproved; target one-NOT input restriction permits onlytwo binary collapses because survivingcofactor ismonotone andneeds16total gates. Globalbinary17 proof inprogress via firstLive retention +automorphisms; AND-first twozero restrictions maygive18binary. SAT firstNOT0 ongoing; twoCEGISattempts UNKNOWN; boundedrepair active. Bv_decide isnot beingused because default compiledreflectionaxiom violates audit. Allcheckedpartialaxiomsauditedstandardthree.

2026-11-25T14:34:18.240911+00:00: checker_storage: Prepared /tmp/oec/pequalnp-pilot-120/checker_storage_keeper.py. Tiny self-test passed byte identity, atomic symlink reads, sealing and write refusal. No real artifact moved and no full cache download yet. Parent requires explicit greenlight after heavy work pauses because cgroup memory reached8GiB. Plan uses only sealed authentic .olean.private data, capped at3GiB initially and6.5GiB memory threshold; pause keeper during cache extraction to avoid file races.

2026-11-25T14:34:26.216931+00:00: circuit_search: OR02/exact3NOT boundary case timed out UNKNOWN after300s. Started full1024-row local SAT repair with7–8 gates free, all others fixed to independently verified9-error near-miss. First9 trials UNKNOWN at10s each; no witness. Repair script free-count adjustment now ensures8 free in future runs. Full-table NOT0 still running toward1200s wall limit.

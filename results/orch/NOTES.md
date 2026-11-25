# Pilot 184: L-meta-10760

Root alone owns the desk lease and git writes. Final PR must add exactly the named Lean file; progress records will be retained in branch history and removed from the final diff.

## Statement

Seven-input graph with edges 02, 13, 04, 14, 24, 05, 15, 35, 06, 26, 36, 56. Show every AND/OR/NOT circuit with fan-in at most two and at most one NOT has an AND/OR circuit no longer. Exact statement is in `/tmp/oec/pequalnp-pilot-184/desk-001.json`. Reductions are not open.

## Shared findings

- Updated CONTRIBUTING requires helper declarations in `PEqualNP.Outside.L_meta_10760` or its `_aux` namespace. Final fully qualified theorem is last, outside that namespace.
- No same graph found in current checked proofs by initial scans.
- Nearby proofs use explicit monotone upper bounds plus certified signed-binary lower bounds, counting a NOT as one extra gate.
- Toolchain and warm cache promised by kit are absent; setup agent is installing Lean selectively within 6.3 GiB free space.

## Replacement strategy

Owned by replacement_proof.

## Lower-bound strategy

Owned by lower_bound.

## Circuit search

Owned by circuit_search.

## Independent review

Owned by status_review.

## lower_bound — 2026-11-25T19:38:14.869680+00:00
Checked 1549 files numbered 10xxx–12xxx: no isomorphic seven-vertex twelve-edge target. Degree sequence [4,3,3,3,3,4,4]. Nearby L_meta_10772 contains generic SignedBuild, double_cut, cut_signed theory (1362 lines); L_meta_10752 has ForestCore certified lower-bound search (4400 lines). Allowed Defs import means copy relevant helper declarations into final namespace instead of importing those files.
Recursive essential-variable restriction bound with triangle=4 and K4=7 signed-binary bases reaches only 9; all false cofactors bound8, degree3 true cofactors7, degree4 true cofactors5. Thus this alone is insufficient for current monotone upper14. Exact existing same-gap PR#16243 source is being fetched by status_review; await it before recreating large certificate machinery. Scratch tree: /tmp/oec/pequalnp-pilot-184/lower-bound/restriction-bounds.txt.

## circuit_search — 2026-11-25T19:38:32.438014+00:00
Simple formula upper14: OR of (x0∨x2∨x3∨x5)∧x6, x3∧(x1∨x5), (x0∨x1)∧(x4∨x5), x2∧(x0∨x4). Exhaustive search of all66 bicliques with shared OR subsets still gives14 (78,745 states visited). Exact target list and isomorphic target absent from915 Fin7 Outside files. C++ stochastic general-circuit13 search running; SAT mono13 CNF ready with boundary rows and symmetry. Root owns lease.

## circuit_search update — 2026-11-25T19:39:32.386384+00:00
Root located exact prior PR#16243 with14-gate witness and signed-binary lower13, matching restricted search optimum. The graph has independence number2: target false only on empty/singleton assignments and9 nonedge pairs; monotone boundary therefore21 rows (12 true edges plus9 false nonedges). genmono.py can use rows,inc,lex for a small38,304-clause13-gate synthesis instance. Stochastic search currently best2 truth-table discrepancies, no13 witness.

## replacement_proof — 2026-11-25T19:40:08.784536+00:00
Initial scan1185 one-NOT proofs found no isomorphic target; exact-edge scan no checked file. Existing L_meta_10770 technique counts binary gates with free negations then pays one for any NOT. SAT→Lean tools in notes/data/lrat-link: gennot.py, genmono.py, genrow.py. Inlining Checker+LinkN+LinkN2+Shannon costs114KB but custom Trie/model structures need manual review or replacement; BinaryTree (Option Nat) is drop-in for Trie. Official CaDiCaL building in scratch. Primary route now profiling existing same-gap PR#16243 (twice timeout): frozen lower-bound/Pruned.lean494450bytes. Root initial cache/build pending; replacement owns --profile baseline, lower_bound owns explicit table/pool optimization.

## circuit_search SAT result — 2026-11-25T19:49:19.517582+00:00
CaDiCaL monotone13 on boundary21 rows,38,304clauses hit its180s wall limit with exit0/no SAT-or-UNSAT verdict.2,075,720conflicts;34.36MB resident. No13-gate witness. Full logs saved in results/orch/lemmas/search/. Exploratory route finished; root prior-PR certificate route remains primary.

### lower_bound: certificate reuse and optimization 2026-11-25T19:54:19.769893+00:00
Existing same-gap PR16243 by MohamadEidAlAktaa contains full signed-binary lower13 + monotone witness14, but both remote checks timed out. Source517777bytes7860lines. Static helper pruning initially missed field notation; corrected closure restores CompactTable.live/bucket and BoundPool.wires, leaving48 unused declarations removed. Corrected Pruned.lean494996bytes7573lines.
FastData.lean precomputes all436 rich-domain entries via85 literal128-bit masks; FastDataGraph.lean additionally memoizes graphGoal127 using the existing graph truth word. Core Lean DomainEquality.lean verifies exact129 main-domain equality and the generic fast-graph equality (exit0, kernel1.76s). Full theorem compatibility/runtime still pending. Root notified to preserve compiled optimization certificate and logs.

## replacement_proof optimization update
Original full source profiling has passed17minutes with no Lean errors, kernel phase1168; RSS3.7GiB. Direct rfl leaf proof slower (8nodes27.49s vs decide+kernel11.56s); domain+graph precomputation no clear speedup. Coverage signature compression promising: first512columns pass1255/1256finalnodes, onlyk7i62fails. Lower_bound exact coverage analysis found131selectedcolumns suffice; candidate pending independent screening.

## replacement_proof — 2026-11-25T20:11:54.171258+00:00
FULL ORIGINAL PR16243 source Lean compile exit0,1286.965seconds(21m26.97). Kernel typechecking1240s, elaboration7.89s, imports6.42s; max observedRSS4.14GiB. Complete stdout/stderr/result copied results/orch/lemmas/replacement/full-original.*. This reproduces posted proof and explains prior20minchecker timeout. Signaturecompression still needed for runtime margin. All22gridcomputationalstates dumped11.7MB scratch TSV to support per-grid hitting-set optimization; lower_bound owns that transformation.

## circuit_search width fallback — 2026-11-25T20:14:06.528513+00:00
Generated ParamWidth.lean generic prefix(155013bytes) parameterizes98 width-dependent declarations and8type aliases; preserves semantic Sig128 and Impossible. Added~5.8KB. Optional type-alias defaults allow earlier grids1024 and finalgrid256 without rewriting earlierdata. Prefix compilationFAILED because mechanical named-width applications in simp/unfold argumentlists must revert to bare identifiers; candidate UNVALIDATED. Root selected all-grid Selected256 instead, so fallback refinementstopped. No activeprocess.

### lower_bound: successful sample-column compression 2026-11-25T20:14:15.982824+00:00
Original PR compiles but exceeds20-minute check cap (replacement measured21m27). Analyzed1256mainstates/413377transitions:30955distinct missing-pair masks,101forcedsamplecolumns,30additionaloptimalcovercolumns. Selected131total. Extended to22grids including everyrawprimitive state; earliergrids need6–89columns. Contrary to initialcount, earliergrids could have700distinctpairs; signatureselection preserves required cuts rather than allpairvalues.
Selected256.lean496125bytes7861lines keeps ORIGINALhelperproofs, changes16signaturewidthliterals and44P/Qconstantfunctions only, addsoriginalauthorattribution. Everychosenindex isoriginal0..1023; unusednew256positionsrepeatavalidchosenpair. Mapping selected-pairs.json and fullPythonselectionlog coverage-selection-validation.txt savedhere. Independentcompiledall-node/primitive screening underway withreplacement; rootwillrunfullkernelbuild/checker.

## replacement_proof — selected-column independent screen
Selected256 has passed compiled screening of2655nodes across22grids and82primitive checks withzero failures. Scratch runner initially included8unused augmentedrootnodes through rawcounts; corrected toactualtablecounts, cleanexit0. AllScreenSelected.leanandcomplete logs backedup inresults/orch/lemmas/replacement. Kernel/fullnamedbuild still required.

## Root strategy review

The full original source compiled in 1286.965 seconds and is backed up at commit 7c4adf03. Selected256 preserves every used certificate check in independent compiled screening and passes exact-statement/format review; its named-file build is running. Width reduction alone improved the sampled kernel benchmark by about 11 percent. Direct rfl, whole-node cbv, and simple chartAt cbv staging were not adopted.

Research read 2026-11-25: Lean official tactic reference, https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/: "The proofs produced by cbv only use the three standard axioms." This motivated a standard-tactic experiment; it did not authorize custom code, additional axioms, or extra proof-file options.

### replacement_proof — staged normalization benchmarks

Whole-node `cbv` fails default 100k steps. Staging chartAt using `conv at hs => rhs; cbv` compiles but 8 sample nodes take 7.47 s kernel versus Selected256 baseline 5.76 s. Staged preCov takes 7.8 s kernel; literal chartAt with a checked `decide +kernel` equality improves only to 5.43 s and likely exceeds remaining source space if generalized. Thus no staging variant recommended. All runs use allowed limits only; complete logs under scratch replacement/. No microbenchmark process remains active.

## circuit_search pool ordering — 2026-11-25T20:24:59.286813+00:00
The data-only candidate PoolOrdered256.lean is 496125 bytes and changes 27 existing packed Nat hexadecimal literals. All helper and theorem text is unchanged, and each node retains its original pick multiset. A compiled pool dump (5.4 MB) and Python transition model give 328948 → 309289 pool checks: 19659 saved, or 6%. Final ax127 was already optimal; savings come from 495 earlier-grid nodes. Storage analysis found 2385 unique spans, 89 shared spans, and no partial overlaps; the changes affect 495 unshared spans. Independent compiled screening was requested from replacement. The candidate is NOT kernel-validated. Sources and reports are in the search folder; the full raw pool dump is scratch/all-pools.tsv. No active process.

### lower_bound: width 128 and constructor forcing — 2026-11-25T20:30:59.399553+00:00
Constructor-forcing identities and eight node proofs compile, but measured kernel time 7.56 s versus earlier 5.76 s showed no speedup under concurrent build load. Artifact ForceSamples.lean and validation log preserved; not integrated.
Selected128.lean keeps the original proof and drops only original sample columns 69, 72, 83 from the 131-column main selection. Exactly three branches become newly uncovered; existing pools 59, 75/791, and 72/408 reject them, verified by the existing Python cachedPoolCut port. Earlier selections remain unchanged, all below 128 columns. Source 496068 bytes, 7861 lines. Independent Lean screen pending; Selected256 remains frozen.
Filtering all coverage constraints already rejected by pools reduces the final selection to 113 columns, with 87 forced. Thus this route cannot reach 64 bits without considering links as well. Dropping only three columns should preserve faster coverage pruning than the more aggressive 113-column selection.

### replacement_proof — alternatives screened after named build

Selected128 and PoolOrdered256 each passed all 2,655 used nodes and 82 primitive checks in the independent compiled computational screen (TOTAL_BAD 0, exit 0). These are not full kernel builds. Complete sources/logs are in results/orch/lemmas/replacement/. Plain decide passed 8 proof samples but took 20.94 s: 10.2 s tactic normalization plus 6.92 s kernel, compared with the previous +kernel baseline 11.4 s wall/5.76 s kernel. Conv dsimp staging also passed but offered no speedup. No tactic replacement is recommended. No Lean process remains active from this agent.

## Petersen lower-bound route 2026-11-25T20:49:35.481268+00:00

- Prepared `results/orch/lemmas/petersen-lower/FiniteGraph.lean`: finite graph facts (15 edges, degree 3, no triangles or squares, independence number at most 4, vertex-cover cardinality at least 6), and a semantic proof that the free nonedge seed may be set to false in any AND/OR circuit computing the Petersen edge function, even for an arbitrary input map. Compilation is deferred while root runs the official checker.
- The star-cover arithmetic certificate is explicitly limited to star-cover constructions; it does not establish a bound for arbitrary circuits.
- Generic existing ReadersExport fanout elimination gives 3 gates at false or 4 at true. This is insufficient for the remaining L7217 premise, which requires 4 at false. L658 needs a good leaf/run-of-four hypothesis that the initial cubic Petersen graph fails.
- Structural counting observation, still unformalized: a connected normalized circuit of g gates and q NOT gates has at most g+1-q input-edge occurrences. If every one of the eight vertices outside {0,2} has two readers, there are at least 18 variable reads plus one if the seed is used. Thus a used seed and any NOT force a read-once outside vertex at g<=18. Without a used seed, two NOTs suffice. Zero-NOT and a tight one-NOT formula remain separate cases.

Counterexample search, L-meta-1890: baseline stochastic18-gate search plateaued at10 falsepositives/0 falsenegatives onall1024rows; stopped to diversify. progress best 10 eval 272445234 runs 29979 elapsed 150.097

### Additional lower-bound observations 2026-11-25T20:53:01.448630+00:00

- A numerical spectral-sensitivity check using all 76 false assignments gives squared operator norm approximately 10.772; that formula lower-bound method does not reach the 19-leaf tight case. This is computational exploration, not a Lean theorem.
- Alternative counterexample topology sent to the search agent: with free seed s=x0 AND x2, H=F OR s and G=F restricted to x0=x2=true, the identity F=H AND ((NOT s) OR G) holds. Here G is the OR of x1,x3,x4,x5,x7,(x6 AND x8),(x6 AND x9). No improved construction found.

### Checked Petersen partial 2026-11-25T20:56:44.231514+00:00

FiniteGraph.lean compiled successfully with the canonical `import PEqualNP.Defs`, exit 0, 25.536 seconds, peak RSS 3145820 KiB. SHA256 `86947eab4079809f74e045ce6e2a962ef0dcc49ee9f68835c45c5b74a9639f2e`. Contains finite graph certificates and a circuit-level proof that monotone seed removal is sound for every input map. No full arbitrary-NOT lower bound is claimed. Complete diagnostics saved beside the source in validation.txt.

## Petersen circuit search — 2026-11-25T20:57:04.650530+00:00
New gap L-meta-1890. Independently constructed a 20-gate Petersen edge circuit and verified every one of 1024 inputs; data in petersen-search/twenty-gates.json. Seeded 18-gate SAT on 30 boundary rows found a model in 14.9 seconds, but full validation found 33 false positives and 868 false negatives. Adding 40 diverse rows led to UNKNOWN after 180 seconds, peak 91.89 MB. Localized SAT repairs of the counterexample agent’s four-error candidate are running, with a 300 MB RSS cap.
Surjective.lean now uses only PEqualNP.Defs and proves that any computing input map must be surjective, using explicit edge witnesses whose x0 AND x2 seed stays unchanged. Initial proof had a corrected Bool-precedence error; subsequent -M2000 runs were blocked by memory limits. Waiting for the sequential -M6500 compilation slot; no claim of a checked theorem yet.

### replacement_proof — Petersen input transport and accepted support

Canonical InputReindex.lean compiled with the required PEqualNP.Defs import at -M6500/-j1, exit 0, 7.56 s wall, 2,877,200 KiB peak child RSS. Its general lemma rewires arbitrary input maps while leaving any appended tail (including the free conjunction) unchanged, preserving gate count and FanInTwo. The proof is extracted with attribution from lv1xx's accepted R_meta_1890_1 (PR 7680). Source and complete logs are in results/orch/lemmas/petersen-proof/.

The nearest accepted cut is R_meta_1890_47: minor-bound child L7215 is checked, while four-gate elimination L7217 remains open. The exact checked L7215 source is 381,652 UTF-8 bytes and its SHA256 matches the public checked feed. An attributed unchanged support copy and review JSON are saved. Other existing cuts leave AND/OR/NOT branches open. All three reduction seats for1890 are already occupied.

Generic nine-vertex lower bound≥15 is accepted as L3829. A generic≥17 bound is false: a sixteen-gate monotone witness was explicitly generated and checked on all512 rows (scratch minor16-witness.json). No direct generic≥16 file was located; the accepted7215 bound requires a designated first conjunction. Reusing10760's finite checker for Petersen needs a major new search:11initial wires,18remaining counted gates, and72,048 full positive/negative separation pairs. The existing signed free-inversion lowerbound is stronger than the requested counted-NOT model and may not be applicable.

Accepted L1993 supplies a finite obstruction to≤6 AndCount gates with each variable bare at most twice on all15 Petersen maximal independentsets. The missing bridge is reducing an arbitrary18-gate seeded circuit (or the tight monotoneformula case) to that model. Counting15 graph edges as14 OR gates needs a real normalization proof; none of the located generic graph lower bounds applies to Petersen's girth5.

## Petersen local obstruction — 2026-11-25T20:59:25.245727+00:00
Independent SAT found UNSAT for the four-gate repair subproblem Y=(x0 AND x5) OR (x2 AND x3) OR (x6 AND x9) OR (x4 AND D), with A=x0 OR x2 OR x6, B=x3 OR x5 OR x6, C=x2 OR x5 OR x9, D=x0 OR x3 OR x9 available freely. Seven relevant original inputs, the free x0 AND x2 seed, and all four pair intermediates are available; each intermediate can independently choose one of three OR pairs, covering all 81 shared-prefix variants. All 128 rows were encoded. CaDiCaL reports UNSAT in 0.64 seconds, 6895 conflicts, 10.74 MB RSS. Counterexample agent’s independent C++ enumerator agrees. This is a restricted topology obstruction, NOT a Lean proof or a lower bound for the whole gap. Generator and complete logs are preserved in petersen-search/.

## Petersen surjectivity checked — 2026-11-25T21:02:23.112116+00:00
Canonical petersen-search/Surjective.lean compiled successfully with lake env lean -j1 -M6500: exit 0, stdout and stderr empty. It imports only PEqualNP.Defs and proves computes_surjective for any circuit computing the seeded Petersen function, with no fan-in or size assumptions. This is a checked helper, not a proof of L-meta-1890. Full logs and validation are preserved beside the source. Root notified for immediate independently reviewed backup push. No active processes remain from circuit_search.

2026-11-25T21:02:36.559074+00:00 — Counterexample search found an18-gate approximation with only four false positives, no false negatives; frozen source and independent full validation in petersen-counter/. Exhaustive local repair enumeration across81 OR-prefix variants and independent SAT both found no repair with four gates. This does not prove the full gap. Exact20-gate upper-bound Lean source rewritten algebraically after its initial giant decision proof was killed(exit137).

2026-11-25T21:04:45.282772+00:00 — Explicit20-gate Petersen upper-bound witness compiled against canonicalPEqualNP.Defs, exit0 in5.10seconds. Source TwentyGateWitness.lean SHA256b34214fe26d52caf8ff3e5c09da1de6be1d8868e263bcd30b8ebd492ccadc1c0; full logs twenty-gate-algebra3.*. No counterexample found. All local search/Lean processes stopped before lease release.

### replacement_proof — L1904 route census and ranked minimum

Structured GitHub census returned zero open PRs matching1904. Three reductions are live. R137 leaves singletonNormalization4316 and singletonBudget4318 open; coverBuilder4320 is accepted. R493 leaves singleton-safe minimum5282 and pair-safe conversion5284 open; its existing proof already supplies prefix provenance and the at-most-two-vertex witness lemma. R271 has accepted forest/cycle child5733 and safe minimum-cover upper child5735; only the general cyclic lower bound5737 remains open. Sources, child statements, checked-feed hashes, and public authors/commits are preserved under results/orch/lemmas/clean-and-proof/.

RankedMinimum.lean compiled successfully under the exact Defs import (-M6500/-j1), exit0, 10.91seconds wall, 2,877,280KiB peak RSS. It selects a least-size equivalent Monotone2 circuit and then minimizes any natural-valued rank among those minima. This is general support, not a proof that unsafe AND gates can be eliminated. Complete logs/result and source digest are saved beside it. No Lean process from this agent remains active.

### L1904 local normalization analysis 2026-11-25T21:17:05.881708+00:00

- The first-unsafe-AND witness on at most two vertices is already proved in accepted R_meta_1904_493; no duplicate proof attempted. The singleton and pair normalization children remain open.
- Compiled `results/orch/lemmas/clean-and-lower/UnsafeBypass.lean`, SHA256 `22ae9381d4bc3381c8b171ad567ae45a2fbba33f8cfd0a389eaa3358f06cecef`, exit0 in 5.417s. This refutes only the naive local bypass strategy, NOT L1904. The graph is the path with edges02,03,12. A five-gate circuit has first AND `(a OR c) AND (a OR b)`, true at singleton a, then ANDs with `(c OR d)`. Bypassing to either operand changes the graph function. A different four-gate safe circuit exists and is checked in the same file.
- Research read 2026-11-25: https://pequalnp.com/papers/note-1 section7 says single-level graph-function bounds do not transfer directly to arbitrary monotone circuits. Underlying cited Jukna sources remain UNVERIFIED here because only the allowed-site account was read. This warns against assuming the requested normalization is a routine literature lemma.

### Checked nonlocal diamond rewrite 2026-11-25T21:22:54.161185+00:00

`results/orch/lemmas/clean-and-lower/DiamondRewrite.lean` compiled exit0, SHA256 `1e8956cf8603f13c24bee0af984e4726bb6b361c28bbfd0d6c2779e9e9e8c7d2`, 9.14s. For an arbitrary circuit prefix and suffix, replace consecutive OR(a,b), OR(a,c), AND(the two ORs) by OR(a,b), AND(b,c), OR(a,new AND). Input addresses precede the block; suffix gates and output avoid the changed middle wire. Size and computed function are unchanged. The first OR may be shared arbitrarily. The new AND truth set is contained in the old AND truth set. The remaining global obstruction is exposing this pattern and handling both OR outputs shared; no complete L1904 proof claimed.

2026-11-25T21:25:14.959318+00:00 — L-meta-1904 counterexample search: no counterexample. Shared-CNF extension family classified informally and exhaustively checked through six core vertices; explicit eight-vertex example has a 14-gate unsafe circuit but a smaller 13-gate safe circuit, all256 rows checked. Petersen19 search plateaued at four errors. Theta233 ten-gate search completed372,056,447 evaluations with one false positive only, input{0,1}; frozen candidate independently checked on128 rows, and SAT agent ruled out every two-gate-descriptor repair. No active processes from counterexample agent.

### L1904 strategy closure 2026-11-25T21:28:48.119933+00:00

After more than 20 minutes of direct structural work, lower_bound has two checked components (UnsafeBypass and DiamondRewrite), with singleton-rank strictness proved independently by replacement_proof. The unreduced shared-OR case remains open. The full positive safe-gate exchange plan and exact remaining obstacles are recorded in `results/orch/lemmas/clean-and-lower/README.md`; implementation was explicitly deferred by root to preserve the remaining work budget and seek an available reduction slot. No full L1904 claim is made.

## replacement_proof: checked diamond rank and local normal form

2026-11-25T21:29:49.983453+00:00 — Canonical-Defs DiamondRank.lean and DiamondRankMinimal.lean both compiled successfully. The rank sums active AND gates over all singleton inputs. The exposed OR/OR/AND diamond on primary a,b,c, with b≠c and no suffix read of the changed middle wire, rewrites to OR/AND/OR and drops the rank exactly1. Together with size/evaluation preservation and Monotone2 equivalence, lexicographic minimization yields an equivalent size-minimum circuit avoiding this local pattern whenever the output also avoids the changed wire. The general claim that an arbitrary dirty minimum circuit exposes such a pattern remains unproved. Complete logs and source hashes live under clean-and-proof; no further1904work is active from this agent.

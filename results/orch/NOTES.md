# pequalnp-pilot-94 — L-meta-1904

Own lease issued 2026-11-25T13:45:00.003Z. Root alone manages desk and git.

Strategies: structure (gate transformations), counterexample (finite and semantic checks), lemmas (existing results/minterms), root (formal integration), status (toolchain and final review).

Only final target lean/PEqualNP/Outside/L_meta_1904.lean belongs in PR diff.

## Research 2026-11-25T13:47:06.917051+00:00
- Read project primary note at https://pequalnp.com/papers/note-1 (web search returned its full indexed body, 2026-11-25); local source notes/note-1-edge-function-exact-size.md agrees on scope.
- Existing exact |E|+tau-1 results cover forests, cycles, and long-thread graphs. They do not cover arbitrary girth>=5.
- The note distinguishes monotone FORMULA and single-level lower bounds on triangle/C4-free graphs from unrestricted monotone Boolean CIRCUIT bounds. It cites Jukna TR05-021 showing single-level bounds do not transfer in general; it says no superlinear explicit edge-function bound is known for unrestricted monotone circuits. These cited original papers were not independently opened (UNVERIFIED beyond the project note).
- Consequently, do not assume |E|+tau-1 for arbitrary girth>=5 as a known lemma. A proof of target may settle the difficult normalization underlying that claim. No external ready-to-formalize proof found on allowed hosts.

2026-11-25T13:47:13.778147+00:00 — lemmas strategy: existing R_meta_1904_493 proves generic small-support safety criterion. Extracted results/orch/lemmas/pair_safe.lean (149 lines), PEqualNP.Outside.L_meta_1904.pair_safe_implies_safe. If all AND gates are safe on supports of size at most two, all are safe globally; no girth hypotheses needed. Compiler validation pending. Remaining difficulty is producing a minimum circuit safe on those small supports. The three live reductions are _137 (singleton normalization/budget/cover builder), _493 (singleton then pair normalization), _271 (forest/cycle cases + general upper/lower).

2026-11-25T13:49:24.221517+00:00 counterexample strategy: audited Circuit/Monotone2. Missing/future wires read false; empty/unary gates allowed, but no immediate existential-minimality loophole. Empty graph admits zero-gate safe circuit.
C5 sanity search: exact Boolean-circuit MILP using edges and maximal independent sets found 6-gate model INFEASIBLE in 69.42 seconds,31,655 nodes. Restricts to useful fanin-exact2 gates and acyclic indexing; normalization not Lean-proved here. Standard 7-gate safe upper bound remains. Full script and stdout in /tmp/oec/pequalnp-pilot-94/counterexample/.
Next target theta(2,3,3):7 vertices,8 edges,alpha3,tau4,expected safe size11. Searching10 gates capped240 seconds, graph automorphism first-pair symmetry. Petersen:10 vertices,15 edges,alpha4,tau6,expected20;15 maximal independent sets.

## Structural route — 2026-11-25T13:49:27.556887+00:00
- Monotone2 allows AND/OR gates of arity 0,1,2 and forward references reading false. IsAO2 normalization is separate.
- Three existing reductions R_meta_1904_137/_271/_493 fill the live reduction quota. _493 proves pair safety implies global safety; lemmas agent is extracting it.
- L_meta_8305 proves exact repairFew from R_meta_2658_412: a dirty AND essential on at most one edge pair can be replaced by a clean edge AND, preserving function/size and decreasing junk. Thus lexicographic minimization reduces to dirty gates essential on at least two distinct edges.
- No L_meta_8307 file exists in fetched upstream; likely unrepaired many-edge case. R_meta_5284_263 reduces pair safety to a still-open exchange decreasing the number of dirty ANDs accepting multiple edges.
- L_meta_8313 gives only existence of a least circuit: singleton-safety predicate is let-bound but absent from its conclusion. It cannot discharge singleton normalization.
- EdgeFnFinal proves lower bounds for much stronger T7 class (cycles and branch-vertex distances at least seven); no implication from girth at least five.
- Direct exchange obstacle: first dirty AND has OR-only provenance on independent inputs. Cross-product of its input supports may cover several valid edges along with nonedges; later shared AND gates can filter these. Replacing it by one clean edge handles only one essential pair. A simultaneous exchange or stronger graph accounting is still needed.

## Reduction tree 2026-11-25T13:51:32.634202+00:00
- No completed assembly path. Direct _137 children 4316/4318 remain conjectures, 4320 checked. Direct _493 children 5282/5284 remain conjectures. Direct _271 children 5733/5735 checked, 5737 conjecture.
- Checked 4320: arbitrary vertex-cover honest circuit upper bound (373 lines, only Mathlib + Defs); checked 5733: forests/cycles least honest circuit (5894 lines); checked 5735: minimum-cover honest upper witness (397 lines).
- Checked useful grandchildren:8237 bypassing a singleton-active gate in a least circuit loses a disjoint edge;8313 least monotone circuit existence;8600 all-false AND cleanup;8149 cover budget if every AND is safe or accepts at most one edge. Their remaining partners are open:8239 singleton surgery;8315 adding singleton cleanliness to least existence;8602 zero-clean to singleton-clean;8151 decreasing multi-edge junk.
- Exact records and statuses preserved in /tmp/oec/pequalnp-pilot-94/research-tree.md and research-lemma-<id>.json. Source static public https://data.pequalnp.com/data/desk/gaps.json; no lease endpoints called.

2026-11-25T13:52:23.321782+00:00 counterexample: bundled CaDiCaL now used via compact circuit_sat.py. C5 optimum7 with any dirty AND is UNSAT(0.319s,462vars2615clauses); control honest7 SAT(0.008s), witness checked all32inputs. These are external solver findings, not Lean-certified. Graph symmetry and useful binary-gate normalization restrictions stated in script. Theta optimum11 with dirty AND search ongoing capped180s.

2026-11-25T13:55:15.775949+00:00 counterexample: theta10 MILP timeout240s(no witness); CaDiCaL theta10/Petersen19 running capped300s. Auxiliary theta11dirty interrupted to keep≤2 solvers. Added candidate K4 subdivided on4edges leavingmatching untouched:n8,m10,girth5,alpha4,tau4,safe upper13; will search12.

2026-11-25T13:55:51.832171+00:00 — lemmas singleton strategy: results/orch/lemmas/singleton_triangle.lean compiles with lake env lean, exit 0, empty stdout/stderr. New invariant singleton_overlap_orientation: for monotone A,B,T, if A AND B AND T implies graph edge and A,B both accept singleton a, triangle-freeness forces singleton-support(A) disjoint singleton-support(T), or singleton-support(B) disjoint singleton-support(T). Otherwise witnesses b,c force edges ab,ac,bc. This is a necessary local condition; it does not prove deletion/bypass preserves full circuit function. L_meta_8313 was checked and its singleton predicate is unused: it only proves minimum existence.

2026-11-25T13:57:53.273651+00:00 counterexample searches STOPPED on root notice of lease410. Theta10/Petersen19 CaDiCaL terminatedSIGINT at13:57:44, no candidatefound; incomplete searches do not establishlowerbounds. All stdout/stderr saved in /tmp/oec/pequalnp-pilot-94/counterexample/. No new workuntilrootconfirmsnewlease.

## Current held step L-meta-2583

Own newlease issued13:59:02 after L-meta-1904 lease disappeared. Only root manages desk. Read1 projectiveplane incidence normal form is newgoal; previous checkedpartials archived.

[2026-11-25T14:02:27.477949+00:00] pilot94_research
## Plane read-1 research (L-meta-2583)
- Public record https://data.pequalnp.com/data/lemma/L-meta-2583.567fbafe0560.json was read on 2026-11-25. It is a conjecture with no dependencies/attempts. Fresh head generated13:58:57Z and search shard2 has no2583 child key; no local R_meta_2583 files found.
- Checked general construction L_meta_7684: every bipartite edge set E and vertex cover A,B admits AO2 read1 circuit size at most |E|+|A|+|B|-1. Taking all N points yields plane upper bound N*(q+2)-1. 1126 lines,51588bytes, imports only Mathlib and Defs; source https://github.com/brilliant-hq/pequalnp-proofs/blob/main/lean/PEqualNP/Outside/L_meta_7684.lean . Helpers t3692 (builder) and t6579 (read1).
- Checked reverse bound L_meta_7639: C4-free E with perfect matching, AO2 correct read1 C => |E|+N <= C.size+1. Combined with plane regularity/perfectmatching gives read1 optimum exactly N*(q+2)-1. Source https://github.com/brilliant-hq/pequalnp-proofs/blob/main/lean/PEqualNP/Outside/L_meta_7639.lean .
- Therefore target can follow from the unrestricted lower bound N*(q+2)-1 <= C.size; conversely target plus7639 proves that sharp unrestricted lower bound. This is a mathematical inference, not an already checked theorem.
- L_meta_4897 gives cover-budget for arbitrary C4-free bipartite graph under read1. L_meta_6579 proves read1 when every AND takes a point-only OR-cone and line-only OR-cone. No checked arbitrarycircuit normalization found. L_meta_2581/read3,1942/read2,2058/read2 give weaker lower bounds only under read assumptions.
- Project note notes/note-1-edge-function-exact-size.md says graphfunction results known to project are formula/singlelevel lowerbounds and exact longthread classes; no general plane normalization proof. Original external papers cited there were not independently opened under allowedhost restriction; their applicability is UNVERIFIED.

2026-11-25T14:02:55.870202+00:00 — Structure2583: copied and Lean-checked selfcontained exact plane star builder from Outside/L_meta_2393 lines4175–4804 into results/orch/lemmas/plane_upper.lean (targetnamespace PlaneUpper). `upper` yields AO2 + correct incidence function + READ1 + D.size+1=N*(q+2), assuming N>0 and q+1 points/line. `from_exact_lower` now proves the target conclusion from N*(q+2)≤C.size+1; both checked exit0. Conversely L_meta_2237 charges READ1 C4-free graph circuits by |E|+vertex-cover, and regular incidence has mincover N, so target is equivalent to this exact unrestricted monotone lowerbound. No cheap read1 semantic shortcut identified.

2026-11-25T14:03:58.095747+00:00 L-meta-2583 counterexamplework: ReadK1 is perprimeimplicant joint proof-tree leafmultiplicity, not fanout. Checkedlower L_meta_7639 gives E.card+N≤C.size+1 forC4free balancedbipartitegraph withperfectmatching andReadK1. HenceFano21edges,N7 read1minimum27, withstarupper verified all16384inputs+21readvectors(Python,notLean).
Fano incidence p−l mod7∈{0,1,3};37maximalindependentsets,21positiveedges. Ordered26gateSAT running;unordered26stopped after~105s to replace withK4incidence14gate search. Fourlines{0,1,2,4} formonce-subdividedK4: any14gatecircuit extendsvia3remaininglinestars+3ORs tofullFano26. Allsources/logs in /tmp/oec/pequalnp-pilot-94/plane-counterexample/.

2026-11-25T14:04:43.601640+00:00 — L-meta-2583 geometry: compiled plane_geometry.lean, 82 lines, same namespace2583, empty compiler logs. Exact hypotheses imply q+1 lines per point by counting all other points in unique-line fibers of size q; no4cycle, at-most-one common point of two lines, and no isolated point/line. Existing sources L1721 and L1719 supply the counting patterns. Hall-based perfectmatching extraction is in progress (targeted official Hall.Basic cache fetched successfully, own compressed cache cleaned). No weak-hypothesis counterexample found.

2026-11-25T14:05:15.163026+00:00 — L-meta-2583 perfectmatching: plane_matching.lean compiles (49 lines, empty logs). Positive regular incidence relation on equal finite sides has matching permutation by Hall and edge-count double count. Combined with plane_geometry.lines_through gives the matching prerequisite of checked L7639. Also incidence_card rewrites total incidence count as sum of rowdegrees, hence N*(q+1). Hall.Basic targeted official cache fetch succeeded; compressed task cache cleaned. Remaining target is the sharp unrestricted lower bound N*(q+2)-1; these geometric facts do not prove it.

[2026-11-25T14:07:37.542192+00:00] pilot94_research
## Broad lower-bound census for2583
Scope: local upstream snapshotecce0276, all Outside L_*.lean containing Circuit or Monotone selected with rg-l. Parsed2949 finaltheorem declarations from2951candidates; the only two without finaltheorem are currentworking partials L_meta_1904 andL_meta_2583. Complete extracted declarations saved all-circuit-final-statements.json in plane-research scratch.102 plane-shaped statements (quadraticN axiom),446 potential tail-lowerbounds,46 edge/incidence-card-plus-budget candidates. No unconditional theorem yielding N*(q+2)<=C.size+1 found.
Closest sharp candidates and missing hypotheses:
- L_meta_8933 (mainline1468;1476lines71961bytes): NoFourCycle+AO2+correctness+nonempty => exact edge-plus-coverbudget if NO unsafe AND fires on TWO distinct edges whose read1 tests bothfail. This weaker condition may provide an alternative core to fullread1 normalization.
- L_meta_7241 (main921): requires every AND false on all nonedge pairinputs.
- L_meta_8569 (main966): leastAO+TopForm+emptyjunk.
- L_meta_4606 (main687): every AND's inputs are in OR-only inputclosure.
- L_meta_7649: every wire notBelowOutput must be OR with children also notBelowOutput; gives starcover decomposition.
- L_meta_8951: has desired coverconclusion but assumes secondgate absent, hence onlytrivial circuits.
- L_meta_1956 has(q+2)*N bound but assumes a universal precursorbound and zero-point/zero-line-degree restriction at everyAND;1955/1958 also conditional assemblytheorems.
- L_meta_3525/1737 exact edge+cover require acyclicity.
- L_meta_3706 gives edge+cover minus countofreadtwiceedges, so the same missingcore remains.
Unconditional weaker bounds applicable toplane:
- L_meta_2988 (main986;1026lines47005bytes):3*N<=C.size+1, merelyMonotone2 andcorrect pairinputs.
- L_meta_8805 (main2293):same3*N bound from genericincidence rejection.
- L_meta_5351 (main3191):349*N<=100*C.size whenq>=200.
- L_meta_1778/3308:atleast2*q^2+1 ORgates;L_meta_3499 converts plusANDlowerbound to4*q^2+2+N<=2*C.size (ordered-input assumption).
Finiteq3 sharp64 candidates1751/2420/5158/5162/8791/2059 all require restrictedANDnesting/line-degree/emptyjunk; none unconditional. FiniteFano1483 gives only20gates.

2026-11-25T14:07:51.674115+00:00 FanoSATsymmetry audited by enumerating336graphautomorphisms:91inputpairs split42samepart,21incident,28nonincident; representatives(0,1),(0,7),(2,7)minimal by(max,min). BothactiveSATsearches remaininconclusive. Prepared independent stochasticlocal-search implementation initialized from27gateFano/15gateK4incidence upper circuits; willrunafterSATslotfree.

### 2026-11-25T14:12:26.161892+00:00 counterexample search, L-meta-2583
- Ordered exact SAT found no Fano 26-gate witness before its 480 s cap (7254 variables, 149801 clauses), and no K4-incidence 14-gate witness before its 480 s cap (1918 variables, 22637 clauses). Both UNKNOWN, not UNSAT.
- Exact monotone checks use all minimal positive edges and maximal independent negative sets: Fano 21+37=58 vectors; K4-incidence 12+12=24. Any SAT or local-search candidate is additionally checked on every input.
- First Fano local search reached distance 1 but only misses edge {1,12}; 47 of 16384 truth-table inputs are wrong. This is not a counterexample. Weighted-positive local search is being prepared to escape missing-edge traps. Full artifacts are under /tmp/oec/pequalnp-pilot-94/plane-counterexample/.

### 2026-11-25T14:15:59.968235+00:00 finite-search update, L-meta-2583
- Fano26 and K4-incidence14 randomized local searches each completed 240 seconds without a witness. K4 checked 2,858,078,888 mutations / 60,591 restarts; its nearest circuit misses edge {2,7}, so 13 of 1024 inputs are wrong. These are heuristic searches, not lower-bound proofs.
- Weighted Fano search preserves every required incidence but best candidate still has two extra nonedges {0,8}, {4,13}; exhaustive 16,384-input check identifies 23 prime pairs and no other prime implicants. This 26-gate circuit computes the wrong graph and is explicitly not a counterexample.
- Independently reviewed root fixed-edge squarefree-proof SAT encoding; exact three-state recurrence is correct. Computed 16-element stabilizer of fixed edge {0,7}, 14 pair orbits saved fano-edge-stabilizer.json.

Fixed-edge SAT strategy: three squarefree proof states track singleton point, singleton line, and pair. Tiny controls passed: one-edge one-gate READ1 SAT; same circuit required unread UNSAT; five-gate path4 unread SAT with full truth-table verification. Full Fano run fixes unread edge(0,7), uses its16-element automorphism stabilizer, and omits gate-order symmetry.

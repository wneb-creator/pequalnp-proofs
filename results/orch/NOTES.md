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

2026-11-25T14:20:35.022472+00:00 — Structure2583: new checked plane_hexagon.lean (75 lines) proves dual unique line intersections from regularity and unique joining lines, then induced6cycle completion of two noncross incidences. New checked plane_three_lines.lean (97 lines) proves that ≥3 lines through p avoid any two other points, then: monotone A∧B∧T below incidence F and T accepting those singleton lines imply either A or B has point-singleton support contained in {p}. Both lean checks exit0 with empty logs. This requires actual singleton-line context acceptance, not just essential edge acceptance; a context rereading p need not satisfy it. PureOR parent counter A=p∨a, B=p∨b with I a b shows neither operand need equal p: g=p∨(a∧b). Sharing the parent ORs blocks the straightforward 3-to-2 gate rewrite. No full normalization or exact lowerbound yet.

### 2026-11-25T14:23:13.028007+00:00 diversified searches, L-meta-2583
- Positive-weight-8 Fano local search: 240 s, 1,554,897,356 mutations, best correct-positive overapproximation has 10 false maximal-independent sets. Weight 64 also finished without a witness; best correct-positive distance 12.
- Constructed and exhaustively checked a correct 29-gate Fano circuit with no READ1 proof on edge {0,7}; this is longer than the known 27-gate READ1 upper bound and is not a refutation. It supplies dirty double-star seeds for search. Artifact: plane-counterexample/fano29-unread-template.json.
- Current diverse 26-gate local search mixes random 27-gate star trees on either bipartition with the dirty 29-gate seed, deletes to 26, and penalizes READ1 on fixed edge {0,7}. Root independently runs exact SAT with the same fixed-edge condition.

2026-11-25T14:24:21.187671+00:00 — Structure2583: checked plane_shared_or.lean (31 lines) formalizes collective repair identity for arbitrary Bool context H: replacing every g_i=(p∨a_i)∧(p∨b) by p and OR-ing b∧OR_i a_i preserves H whenever that added star is below original output. H need not be monotone. Circuit deletion/remapping and r+1 gate budget are not in the lemma. For ORdescendants p∨OR(S_j) of common p∨b with safe rectangles a_j×S_j, C4freeness makes S_i∩S_j={b} for distinct centers; extra ORcone sharing is confined to one center. Extending repair still requires charging aggregation gates against removable parents or already READ1-covered base edges.

[2026-11-25T14:28:40.455267+00:00] pilot94_research
## Boolean-versus-bilinear research conclusion
No rigorous C4-free bipartite counterexample or general sharp normalization theorem found. A generic theorem for all bipartite graph functions is ruled out by checked local L_meta_3679: explicit39vertex bipartite graph,58gate AO2 circuit, but every circuit with noANDancestorAND has>=59gates (Joined3679.flat_lower, line1223). ExplicitC4 is29-6-30-9-29. Hence this refutes genericBoolean-to-separated normalization, but nottheC4-free target. Source: https://github.com/brilliant-hq/pequalnp-proofs/blob/main/lean/PEqualNP/Outside/L_meta_3679.lean .
The local4849 counterexample concerns anunsafeAND in a minimum11gate C3/C4-free graph, but its5cycle0-4-7-1-6-0 makes it nonbipartite; it disproves only the assertion aboutEVERYminimumcircuit, notexistenceofacleannormalform.
Pure-theory child c4free_theory finished: P4 edgefunction ab OR bc OR cd equals ((a OR c) AND(b OR c)) AND(b OR d). This5gate circuit hasonly3leafproofs for2variableedges, so isn'tread1. BypassingitsmiddleAND tofirstoperandintroducesad; bypassingtootherintroducessingletonb. Ordinary formaldegree2homogenization erases allterms (formalexpansioniscubic); Booleanidempotence isessential. Nevertheless4gate read1 b AND(a OR c) OR(c AND d) exists. This demonstrates whylocalbypass/homogenizationisnotaproof, notacounterexampletotarget.
Webread2026-11-25:
- https://github.com/open-goat/pequalnp-proofs/discussions/9111 : replyreports fullreadingofLenz-Wegener1991; itsresults countANDsonly, bicliquecovercharacterizessingle-levelANDcount, and itdoesnotgiveexacttotalgatecost. Theoriginalpaperwasnotopenedunderhostrestriction; itsclaims remainindependentlyUNVERIFIED. Discussiongives noC4-free normalizationtheorem.
- https://github.com/open-goat/pequalnp-proofs/discussions/8193 : contributor suppliesLean cross-AND witnesses andBelowFsupport-starproperty, expresslynotasizebound. NonBelowFANDsremainuncontrolled.
- https://github.com/open-goat/pequalnp-proofs/discussions/9816 : maintainer confirmsHeawoodseparator25gateboundstillopen; discussedrestricted58testsearchdoesnotresolveplane27gateoptimum.
- https://github.com/open-goat/pequalnp-proofs/discussions/12644 : authorreports no smallcore-coverviolation and unsuccessfulPG(2,3)63gateannealing, withfailed70gatecontrol; thisisweaksearchdata, notlowerboundproof.
- https://pequalnp.com/papers/note-1 section7 reportsJukna2005Problem24: explicitgraphfunctionsuperlinearmonotoneboundwasopen; itdoesnotclaimcurrentliteratureiscompletelysurveyed. OriginalpaperindependentlyUNVERIFIED. OurplaneclaimwouldgiveOmega(n^1.5) forinputcountn=2(q²+q+1), explaining whyaquickgenericnormalizationisunlikelytoalreadyfollowfromformula/arithmetictheorems; thislaststatementisinference, notimpossibilityproof.

2026-11-25T14:29:11.235461+00:00 — Structure2583 substantive cost routes (mathematical arguments, not Lean checked): (1) Closed mixedOR-descendant cluster from B=p∨b with readers g_i=(p∨a_i)∧(p∨OR S_i), b∈S_i and all a_i×S_i incident. If every later firstAND context is pureOR, its lines must all pass through p, so each nonlinear branch can transmit only a_i k_i for the unique joiningline(p,a_i). If p lies on b, all k_i=b and collective star repair pays with rootB+reader gates. If p not on b, distinct a_i on b give distinct k_i≠b. Their mixed parents D_i must be distinct nonrootORnodes (sharing would give C4), paying matching-edge reconstruction: delete ≥r+1 ORs and ≥r ANDs, add r edgeANDs plus r ORs including finalOR. Nested unsafe/reread contexts remain excluded. Without pureOR contexts localbudget claim is false: B,D1=B∨c,D2=B∨d and two readers delete5 gates, but added P5 a1(b∨c)∨a2(b∨d) needs5 plus finalOR; verified all472 five-input read-once functions, target absent.
 (2) L_meta_3679 uses (6∨7∨8∨9)∧(6∨7∨8∨10)=(6∨7∨8)∨(9∧10), then absorbs extra9∧10 in outputs alreadycontaining9 or10. Savings require commonlinear support≥3. More generally, for a vector oflinearORoutputs with pairwise supportintersection≤2, remove latestAND: singletonsupport size≤2 can be replaced byORofsupport at≤1gate and preservesoutputsingletons; size≥3 reaches onlyone output viaORpaths, and AND below that linearoutput has oneoperand belowit (test complement ofrowsupport), so bypasssafe. Zero-support gates prune asfalse. This should normalize pure-side linear preprocessing toOR-only withoutcostincrease. It does not normalize arbitrary mixed point/line circuits.

## 2026-11-25 14:31:12 UTC — READ1 exact plane bridge checked

Extracted the self-contained READ1 graph/cover lower bound from merged L_meta_7639 into `results/orch/lemmas/plane_read_lower.lean`, under `L_meta_2583.ReadLower` (2038 lines; auxiliary imports own named partial only). New `plane_bound` proves `N*(q+2) ≤ C.size+1` for every READ1 AO2 plane circuit, using the checked regular incidence matching, no-four-cycle property, and incidence count. `fano_bound` specializes this to `27 ≤ C.size`. `replacement_iff_bound` proves the exact replacement conclusion of step2583 is equivalent to the unrestricted numeric lower bound for that C; its reverse direction uses PlaneUpper.from_exact_lower. This does not prove the numeric lower bound for unrestricted C. Confirmation compilation exited 0; full stdout/stderr and explicit exit status are in `/tmp/oec/pequalnp-pilot-94/plane-lemmas/plane_read_lower-confirm.*`. Only inherited linter/deprecation warnings; no errors. Static source scan found no forbidden root marker, quotes, axiom/sorry/native_decide, attributes, options, or theorem keyword. Parent must remove the auxiliary own-module import if integrating source into named file.

### 2026-11-25T14:35:18.146664+00:00 counterexample search updates
- Pair-proof-only SLS penalty was insufficient for incorrect overapproximations: a singleton proof also meets READ1. Corrected to penalize any squarefree proof state. This did not affect exact SAT, whose correct graph output forbids singleton states.
- Subsequent search correctly found wrong circuits accepting an unrelated singleton. Directed phase now penalizes every singleton and both pure bipartition inputs explicitly. No counterexample found.
- CGP controls passed: embed known27 and dirty29 circuits into42 slots, prune unreachable gates, and check all16384 inputs. Recovered27/29 gates exactly with zero functional errors. This enables function-preserving evolution with inactive helper workspace.
- Root resolved exact-size padding: if output F=A op B, append F op A using the same AND/OR operation; absorption preserves F, operand indices are distinct, and one gate is added. Earlier padding caveat is mathematically resolved, though no Lean lemma was produced here.

### 2026-11-25 14:43 UTC — research: split gate counts

Scanned 2733 candidate Outside files, extracting 2731 final theorem statements (the two root partial files were excluded). Full candidate metadata is retained in gate-count-final-statements.json; focused candidate sets are in gate-count-lowerbound-candidates.json, abstract-and-count.json, and or-count-rhs.json. This was a local source census, not a new Lean build.

No theorem found deriving ANDcount >= N and ORcount >= N*(q+1)-1 for every incidence-plane circuit from actual correctness alone.

* L_meta_1778:429 gives the strongest directly applicable general plane OR lower bound located: 2*q^2+1 <= ORcount. Its hypotheses require incident-pair acceptance and rejection of independent inputs with at most q active lines; actual correctness suffices. L_meta_3308:429 repeats this for q >= 200.
* L_meta_599:1264 and L_meta_4837:1263 prove |E| <= ORcount+1 only under every induced subgraph having at most its vertex count, as well as no C4. The plane graph violates the induced-subgraph hypothesis already on all 2N vertices, since N(q+1)>2N.
* L_meta_217:7349 and L_meta_2399:7381 prove ANDcount >= minimum vertex cover only for a cover lower bound t <= 5. Plane N >= 7 is outside this range.
* L_meta_1406:289 proves cover <= ANDcount when every AND gate is below the graph function, exactly an unavailable normal-form condition. L_meta_1407 and L_meta_7848 give the resulting total-size bound under the same condition.
* Explicit Fano graph ANDcount >= 7: L_meta_634/L_meta_910. Explicit PG(2,3) ANDcount >= 13: L_meta_1898:7314, or the abstract set-DAG equivalent L_meta_8750:7395. These are fixed labeled incidences, not an arbitrary plane classification theorem.
* PG(2,4) L_meta_7025:298 assumes ANDcount <= 10 and concludes 21 <= ANDcount; it only excludes counts <=10. L_meta_7838 requires every direct variable pair at every AND to be a graph edge and disjoint sides, so it is not an unrestricted lower bound.
* L_meta_7824 gives 52 <= AndCountCircuit.size+1 for 52 negative and four positive tests, but additionally assumes EVERY gate is true on EACH of the four positive tests. This hypothesis is not implied by output correctness, so dual converter L8043 does not automatically yield 51 OR gates.
* L_meta_529 proves unrestricted multiple-output OR-family complexity sum(|S_i|-1) for pairwise intersections <=1. Extracting all line-neighborhood outputs from one incidence-function circuit is still missing; merely dualizing or setting one point input true does not preserve the gate budget jointly.

Potential false-friend: L_meta_1006 refutes a C4-free graph minimum AND count statement for maximal-independent-boundary tests. The graph contains disjoint triangles and is not bipartite; the theorem does not even claim full graph-function correctness. It is not a refutation of the held gap.

2026-11-25T14:51:35.730116+00:00 — Structure/child latest_dirty_math: verified FanoAND>=7 already proved L634 and stronger boundary versionL910. L910 uses singleton stripping, 9MISrows perpoint giving cofactor>=4AND, occurrencecap2, generic signed-slot no_cover_gt. Therefore six-AND Fano search canceled beforeanysolver. Reviewed freeORdual model nowprepared for K4-incidence originalOR<=10; controls and480s search scheduled after14:52:34 slot.
 Substantive mathematical subclass proof (NOT Lean checked): if everyAND has atmostone operand with a line-input ancestor, trim andview as weightedline-linear network. Anyline-dependentOR musthave twoline-dependentinputs: a point-onlyinput wouldbetrue atX=1,Y=0 and propagate truth tooutput. If rlineORs,alineANDs,Nlineinputs, networkE=2r+a,V=N+r+a. Reversing uses E-(V-1)=r-N+1ORs; reusepoint-onlycoefficientDAG once. Reversecomputes allpoint-neighborhoodORoutputs. L529partitionproof countsONLYORmerges (ANDchoosesfalseoperand atcomplementrow), so reverseOR>=Nq. Thus originalOR>=Nq+N-1. ConstructedREAD1size<=OR(C)+N; no-sizeincrease requiresseparateAND(C)>=N, knownforFano/order3, notclaimedgeneral. This isolates genuine obstruction to AND combiningtwo line-dependentwires. Also allunsafeANDs sharingonesingletonanchor p forces pureOR oppositecontexts aftersafeextraction; obstructionsneedmultipleanchors orsingleton-freeANDs.

2026-11-25T15:04:31.762499+00:00 — Structure search completed: K4-incidence dual10AND (originalOR≤10) unrestricted480.014s UNKNOWN; cofactor-capped/clique-bare110.012s UNKNOWN. No witness/proof. Allcode/CNF/completeoutputs/results archivedresults/orch/structure-search. Controls fixedFano7SAT/C5dual3UNSAT/C5dual4SAT/cliqueC5dual4SAT passed. Searchslotreleasedtocounteragent fornormalizedCGP.


## Structure-agent consolidation for L-meta-2583

### Lean-checked components produced in this job

- `plane_upper.lean` (648 lines): exact AO2/READ1 star construction with `D.size+1=N*(q+2)` from positive N and q+1 points per line; `from_exact_lower` converts the missing unrestricted lower bound into the posted conclusion. Extracted from existing checked L2393 and recompiled in the target namespace.
- `plane_hexagon.lean` (75 lines): regular incidence plus unique joining lines implies unique intersections of distinct lines; two noncross incidences extend to an induced six-cycle.
- `plane_three_lines.lean` (97 lines): three lines through p avoid any two other points. If monotone A,B,T satisfy A∧B∧T≤F and T accepts those three singleton lines, either A or B accepts no singleton point other than p. This does not infer singleton acceptance from essential star edges and does not force either operand to equal p.
- `plane_shared_or.lean` (31 lines): the exact collective Boolean-context identity for readers `(p∨a_i)∧(p∨b)`, replacing them all by p and exporting `b∧OR_i a_i` when that exported star implies the original output. It does not formalize circuit deletion or gate counts.

Each file compiled with Lean exit0 and empty final stdout/stderr. Root integrated/reviewed the relevant components. None proves the full posted statement.

### Mathematical arguments, not formalized here

1. **Decreasing a wire while preserving every valid edge-pair value preserves the full graph circuit.** All minimal true inputs remain accepted; monotonicity supplies all true supersets; decreasing the circuit cannot add false positives. In particular `(p∨a_line)∧(p∨b_line)` can be replaced by p, and `(p∨a_point)∧l` can be replaced by p∧l when a is not incident to l. Fanout does not obstruct these exact pair-preserving decreases.
2. **Closed shared mixed-OR component, with pure-OR contexts.** Suppose B=p∨b, mixed OR descendants D_i=p∨OR(S_i) all contain b, and every removed reader is `(p∨a_i)∧D_i`, with all a_i×S_i genuine incidences. The component has no other external readers. Any pure-OR opposite context in a safe top AND uses only lines through p. Therefore the only non-p edge that a_i can transmit is its unique joining line k_i with p. If p lies on b, the exported edges form one b-star, paid by B plus the removed readers. Otherwise distinct a_i on b have distinct k_i≠b, and their mixed parents D_i are distinct nonroot nodes by C4-freeness. Those nodes and the reader ANDs pay for the exported matching and the final output OR even if parents p∨a_i remain shared. This coupled count excludes nonlinear/rereading contexts.
3. **Why unrestricted local accounting fails.** Three mixed ORs B=p∨b, D1=B∨c, D2=B∨d and two dirty reader ANDs delete five gates. Exporting all four nonlinear edges requires the P5 function a1(b+c)∨a2(b+d), which needs five gates, plus a final OR. Exact enumeration of all472 five-input read-once monotone functions excludes a four-gate realization (all five inputs are essential, so four gates would be read-once). This is a counterexample to that local budget, not to the plane statement.
4. **Common-anchor class.** After safe-gate extraction/TopForm, if every unsafe AND accepts one common singleton p, the opposite operand of a safe top AND must be pure OR. Any unsafe AND ancestor on both sides would make the top gate accept p. The unresolved class therefore includes different singleton anchors or singleton-free unsafe ANDs.
5. **Relative-safe context restriction.** If g accepts singleton p and g∧T≤F, setting all line-neighbors of p to false in T gives a safe function T0≤F. It preserves T on edge pairs whose line is outside p’s pencil. Producing T0 may require copying shared circuitry; no free gate-credit argument was found.
6. **Line-linear subclass.** Assume each AND has at most one operand with a line-input ancestor. Trim unused gates. A line-dependent OR then has two line-dependent inputs, since a point-only input would force output true at all-points1/all-lines0. With N line inputs, r line-dependent ORs and a line-dependent ANDs, the weighted network has E=2r+a and V=N+r+a. Transposition needs E-(V-1)=r-N+1 ORs, reusing the point-only coefficient DAG once. It computes all N point-neighborhood OR outputs. L529’s partition proof strengthens to count only OR mergers: AND requires no merge; a merging OR cannot be charged to two supports intersecting in at most one point. Thus OR(C)≥Nq+N−1. A READ1 construction costs at most OR(C)+N, so no total-size increase additionally needs AND(C)≥N. That AND bound is known for Fano/order3, not established for arbitrary q in this job. Neither transposition nor this refinement was Lean-formalized here.
7. **Existing checked results verified by the theory child.** L634 proves exact Fano free-OR AND complexity7. L910 proves the stronger maximal-independent-boundary AND≥7 using singleton stripping, cofactor occurrence cap2 and signed-slot counting. L8750’s order3 AND≥13 proof is substantially finite/geometry-specific. L529 states the total-gate lower bound for linear outputs with pairwise support intersections≤1. Free-OR singleton stripping may increase actual OR work and does not preserve the target’s total gate budget.
8. **L3679 counterexample mechanism.** It computes `(6∨7∨8∨9)∧(6∨7∨8∨10)=(6∨7∨8)∨(9∧10)` in one AND, then absorbs the extra9∧10 using later outputs already containing9 or10. It saves computing a shared linear intersection of size3 and has C4s. Direct subdivision does not preserve this circuit because it introduces independent per-edge controls. It is not a counterexample to the plane statement.

### Search results and remaining full-target route

The reviewed free-OR encoder was dualized to search K4-incidence circuits with at most10 original OR gates. The unrestricted3300-variable/13772-clause run ended UNKNOWN after480.014s. A3550-variable/18812-clause restricted run ended UNKNOWN after110.012s. Restrictions were point-reader cap2, line-pair reader-union cap3, and clique bare operands; mathematical justifications are archived, not jointly Lean-certified. No satisfying witness, UNSAT verdict, or checked lower-bound certificate was obtained. Controls fixedFano7 SAT, C5dual3 UNSAT, C5dual4 SAT and clique-C5dual4 SAT matched expectations; SAT models were independently checked on every assignment. Complete source/CNFs/results/stdout/stderr/control reviews live in `results/orch/structure-search`.

The full remaining route is still a size-preserving normalization, or the sharp unrestricted bound N*(q+2)≤C.size+1. Existing READ1 lower and upper bounds make that equivalence precise. The strongest structural progress handles closed components with pure-OR contexts and the syntactically line-linear subclass. A general proof must pay for shared nonlinear contexts, or show that remaining unread-edge components have sufficiently restricted structure. No unrestricted counterexample or normalization proof was found. No solver remains in this agent’s slot; it was released to the counterexample agent at15:04 UTC.

### 2026-11-25 — research: new L-meta-4970 ledger census

Only L_meta_4791 among existing Outside files mentions TwoColour/tCount. It transforms a singleton-rejecting AO2 circuit into T=0 at cost D.size+4<=6*C.size; it is not a sharp zero-T ledger.

Closest exact conclusion: L_meta_4990:936 proves E.card+cover.card<=C.size+1, but requires two wire sets P,L closed under OR gates from point/line inputs and EVERY AND gate taking its first operand in L and its second in P. The new star witnesses concern arbitrary circuit gates and do not imply this hypothesis.

L_meta_2234:545 is a useful structural partial ledger. Inputs: NoFourCycle G, AO2 C, output false on every singleton, finite F of indices, maps ctr and lf, and each OR-reach orIn(lf j) lies in neighbors of ctr j. Conclusions: (1) every nontrivial OR gate OR-reachable from these wires is outside the output OR cone; (2) sum over centers of the number of distinct witnessed neighbors is at most the number of those nontrivial OR gates plus F.card. L_meta_2233:215 additionally bounds the number of AND gates OR-reachable from output by output-OR-count+1. Joining these needs top AND ownership/center data absent from the new hypothesis.

L_meta_278:297 is the stronger SEMANTIC support ledger: a wire o has singleton support S, rejects all weight<=k inputs outside S, c<=k, c+1<=S.card; then c is at most the number of gates j whose semantic singleton support is a subset of S and has at least two vertices. Pure OR-of-S witnesses meet these assumptions with c=S.card-1. The counted gates may be AND or OR, so idempotent AND barriers do not defeat the lemma. L_meta_270:307 sums such charges for a family with pairwise support intersections<=1. L_meta_529:251 gives the full multiple-output OR-family bound sum(|S_i|-1)<=gates.length under pairwise intersections<=1 and fanin<=2, with no read condition.

Caution: witnesses from DIFFERENT centers on the same side have support intersection<=1 by no-C4; opposite sides are disjoint. Several witnesses for the SAME center can overlap arbitrarily, and the hypothesis need not supply one circuit wire representing their whole union. Thus simply applying L270 to all witnesses is invalid; a grouped component ledger is still needed. Also semantic pure OR witnesses need not have identical syntactic OR-reach: (b AND b) OR c computes b OR c but has orIn={c}. T=0 does not prevent this masking.

Other exact ledgers L2235/L2237 assume joint read1, and L4183/L1491 require minimum AO circuit plus TopForm and include the unresolved Ustar surcharge. They do not directly apply. No checked theorem assembling the new hypotheses into the exact conclusion was located. Exact selected statements retained in 4970-ledger-exact-statements.json.

## 2026-11-25 15:27:33 UTC — gap4970 semantic star ledger and READ1 obstruction checked

`gap4970_star_ledger.lean` extracts the localized assigned-gate proof from merged L_meta_782; `assigned C T` consists of gate wires whose accepted-singleton support is contained in T and has cardinal at least2. `pure_or_card_assigned` proves Q.card−1≤assigned.card for any existing output exactly OR Q with Q⊆T; `assigned_disjoint` handles support sets intersecting in at most one point. This works for arbitrary monotone implementations, not merely literal OR-reach. 324 lines, compiler exit0, empty logs.

`gap4970_read_obstruction.lean` checks that tCount0 plus the new pure-star service assumption does not imply READ1 of the given circuit: the 3-gate circuit OR(y0,y1), AND(x0,g0), AND(g1,g1) computes the one-centre two-edge star, has tCount0, is not READ1, and its first gate serves each edge. This is an obstruction to that proof route, not a counterexample to the posted cardinality bound. Both auxiliary files use Defs+Mathlib.Tactic only; full logs are in plane-lemmas with matching filenames and explicit .exit.

2026-11-25T15:30:51.004638+00:00

### Structure: checked star-centre selection for L-meta-4970

Checked Lean helper `results/orch/lemmas/gap4970_structure.lean` proves that one semantic pure-star wire with support of size at least two has a unique centre in a bipartite C4-free graph. The proof handles both sides and uses singleton assignments to identify the support; opposite-side linear OR functions cannot coincide. `witness_cover_bound` then chooses all centres witnessed in a finite set J of gate indices, obtaining a vertex cover of size at most J.card. Gate operation and validity may be enforced in J. This conclusion permits unused witnesses and does not assert the full gate bound. Lean exit 0; complete stdout/stderr are empty in scratch `gap4970-structure.stdout` and `.stderr`.

Unresolved ledger: the OR-only preprocessing cost is available from the separate partition helper, but a disjoint lower bound for the remaining computation is not established. A C6 example warns against charging full witness unions twice: compute by three point stars (8 gates), append three unused line-star ORs (3 gates), choose all six centres. Six preprocessing ORs leave five gates, while the naive m+S-1 remainder would demand eleven. The correction must subtract double-covered incidences D, or select/orient the witness family appropriately. This is not a counterexample to the posted statement.

Also, tCount=0 is syntactic: b AND b hides line b from OR-only reach, so a OR (b AND b) has mixed semantic singleton support while no two-colour OR is counted. Any semantic-colour normalization must charge these AND barriers.

## 2026-11-25 15:32:09 UTC — gap4970 OR-only partition bound checked and frozen

`gap4970_or_partition.lean` (315 lines; SHA256 `30d82ea23a5c2bb10a8e19d243d7bdfff656b4a410d350f3442e463b4429a7b9`) adapts merged L_meta_529 partition invariant to count OR gates only. New and_false_parent proves that an AND gate false on the complement of T cannot merge singleton-label classes: choose an operand false there and invoke the previous label invariant. Therefore main_inv bounds T.card by the number of remaining labels plus D.card, where D consists only of OR gates false on complement T and true on at least two singletons. New roots_bound handles any family of existing OR Q outputs with Q⊆T and one representative per connected component of their support-overlap relation; T.card≤representatives.card+D.card. This supplies the connected-component pure-star budget while leaving all AND gates uncharged. It does not prove the remaining output/centre gate budget. Compiler exit0; complete stdout (1965 bytes deprecation warnings), empty stderr, and explicit exit status saved as plane-lemmas/gap4970_or_partition.*. File frozen for independent review; future work will use a separate auxiliary file.

### 2026-11-25 — independent research review

Independent red-team review: APPROVED as partial helpers, not as a complete proof of L-meta-4970.

Reviewer: pilot94_research.
Scope: the frozen StarLedger, ReadObstruction, and Structure helper files; OrPartition was deliberately excluded from this review.

Validation: concatenated the exact helper sources with imports moved to the top in a scratch audit file, appended #print axioms for eight principal declarations, and ran prepared lake env lean. Exit code 0, stderr empty. Every inspected helper depends only on propext, Classical.choice, Quot.sound. Existing individual compile logs were also empty and successful.

Static checks: no sorry, axiom, native_decide, unsafe, partial, opaque, initialize, run_cmd, or elab declarations; no _root_ text, quotes, attributes, or set_option. Imports are PEqualNP.Defs and Mathlib.Tactic on import lines. Each helper is under its gap-specific namespace. No declaration claims the exact posted final theorem.

Semantic review: StarLedger uses actual circuit wire semantics including out-of-range reads false, and its cut proof counts only removed gates. assigned counts wires whose singleton support has at least two inputs and is contained in the target; missing/input wires cannot enter it. pure_or_card_assigned correctly handles the empty support case. ReadObstruction computes a star followed by an idempotent output AND; it disproves the direct READ1 implication while satisfying the star-service condition and T=0. It does not refute the held size statement. Structure proves uniqueness of semantic nontrivial star centers using no-C4, distinguishes point/line supports on split assignments, and constructs a vertex cover of size at most a finite witness set J; J need not be minimal or all live gates.

Provenance: StarLedger inherited run/value/cut/card_assigned toolkit was copied/adapted from merged L_meta_782 (which credits k-sandhu PR149 and notes card_assigned adapted from L270), with new assigned_disjoint and pure_or_card_assigned corollaries. ReadObstruction and Structure are new helper implementations for this job.

Frozen hashes:
- results/orch/lemmas/gap4970_star_ledger.lean: afde4d31f0e2c32ff1d3c2149907c96dc750299a9f4d3a4a98a9c1060fc89168 (325 lines)
- results/orch/lemmas/gap4970_read_obstruction.lean: a9c14fbf33ae8d98181765cd151d087201b2fabd3ba4a28ef9792cf6fe104caa (33 lines)
- results/orch/lemmas/gap4970_structure.lean: 9972ce8a5cc1bd6c065328012355b7b3cb83e51526f31a676d6185f410b85c29 (126 lines)

Audit outputs retained at /tmp/oec/pequalnp-pilot-94/plane-research/4970-review-audit.stdout and .stderr; static data in 4970-review-static.json.

Named integration review APPROVED: lean/PEqualNP/Outside/L_meta_4970.lean, 484 lines, sha256 3b38a082914478f3fd4cce85e6885ca03b47750ca9bb6ee7d2f08101ba83a79e. All three declaration/proof bodies match the independently reviewed frozen sources verbatim after only namespace/import/open relocation. Imports first, one allowed outer namespace, no prohibited keywords, _root_ text, quotes, attributes, options, or claimed final target. Approval is for a compiled partial checkpoint, not completion of the gap.

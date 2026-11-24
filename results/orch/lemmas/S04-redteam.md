# S04 original-shard completeness red-team

Verdict: **PASS, with the precise mathematical scope below.** No unsound cut or current metadata/model mismatch was found. This is an independent source/mathematics review plus bounded composition controls, not a Lean normalization proof, a SAT verdict, or a global refutation. Completed 2026-11-24 about 03:30 UTC, within the requested first 20 minutes.

The implication reviewed is: an original-model circuit computing the posted graph function, having at most 21 gates, first junk AND at index 17 and another junk AND later, gives a model of the specified originalDAG CNF after the reviewed normalizations. The all-live step depends on the clean-circuit lower bound 22 and its constant-propagation extension. Earlier-junk and one-junk circuits are outside this implication. A future `verifiedCNFUNSAT` result for these bytes would exclude this shard under those mathematical reductions; it would not be a Lean global refutation of the posted existential.

## Exact artifact binding

| Artifact | SHA-256 |
|---|---|
| Running originalDAG CNF | `38d93ec59a86378a8434b232d19b2b53e8cbc3c715e81432ee94db59ca6ace08` |
| Current `original-dag-strong/original.json` | `5a430e86affc12584f964af39920201684505bafca4d34c1d30e6a10de3b9f51` |
| Actual `search_l1342_shard17_ancestorreverse.py` | `b10d8832060d1c554fd3daa563b7159d515a3c55adc49718989eaa9bd0c2f24f` |
| Actual `build_original_strong.py` | `9e5ae318f33ff8fea98dd8c4a201c82674023102340fdbe86bd69083419e33f1` |
| Ancestor-support helper | `6bd7f7a2120d7d5446d9609a0551308b224d91d23463354514cefe631803e38b` |

Fresh generation from the repository sources reproduced all 11968 variables and 114566 clauses byte for byte. The generated metadata also equaled the current metadata as a complete parsed object. This checks the original DAG before the generator's fixed-tail rewriting; the seven formula templates do not enter this artifact. The builder's parent metadata is not independently hash-pinned by the builder itself, but the current exact metadata is bound above and reproduced, so this is not a current mismatch.

The actual Lean evaluator was read: unavailable reads are FALSE, nullary AND is TRUE, nullary OR is FALSE, unary gates copy, and output indices are unrestricted. The augmented 13-source binary model can represent every raw gate without increasing its count. Free TRUE makes it an overapproximation; a SAT candidate still requires original-model normalization and gate counting. These conventions do not invalidate the UNSAT direction.

## Normalizations and their composition

Productivity is safe only in the clean prefix. A zero-support clean-prefix operand is false on all independent inputs. Replacing an AND containing it by that operand preserves those values and increases edge values. Cleanliness and suffix junk status therefore survive.

Dominance compares a prefix AND against an earlier zero-support prefix gate. The required comparison is only on the 16 edge rows. Replacing the AND by the earlier gate preserves all independent values and cannot reduce an edge value. The positive witness clauses encode exactly the existential failure of this dominance condition; they do not require the witnesses to be equivalences.

For strict OR, equality to an operand on singleton and edge rows is enough to delete the OR: clean-prefix singleton supports determine all nonempty independent values. Duplicate descriptions and OR aliases can also be deleted. Full-support substitution by free TRUE preserves all nonempty values. It can change an intermediate empty-input value, but the correct output remains false on a singleton, so monotonicity keeps its empty-input value false.

A single decreasing measure resolves interaction between the cuts: prune dead prefix gates, sort the remaining core, and delete a core gate whenever productivity, dominance, duplicate-description, absorbed-OR, or full-support canonicalization fails. Recheck after every deletion and re-sort. Every rewrite removes a core gate; none adds one. Once stable, append the required OR-copy chain exactly once. This avoids assuming that separately valid normalizations automatically commute.

If the stable core has k>0 gates, its last gate must feed the suffix, since it is live and has no later core reader. Pad a chain from that gate and redirect one suffix occurrence through its endpoint. If k=0, use any source consumed by the suffix. Every padded copy is live, has a fresh description, and has maximum operand index above all core descriptions. Copies are exempt from strict OR and full-support restrictions, add no ANDs, and occur after every core AND, so they create no new earlier dominance comparison. The four suffix operations and their independent-input values remain unchanged and regain indices 17–20.

Lexicographic ordering by `(right,left,AND-first)` is schedulable: emit the least available key. A newly enabled gate references the just-emitted output, whose wire index exceeds all older operands; its primary key cannot undercut the emitted key. Equal operand pairs can occur for opposite operations, but equal full descriptions are removed. Actual lex equality flags are one-way implications; unequal pairs must be allowed to choose FALSE. The tested auxiliary extension makes that choice explicitly.

The prior output-last/all-live case split was re-read, including the exceptional first-live-junk-at-19 case. If gate 19 is AND(18,18) and 18 is a dirty OR, deleting that alias leaves a clean output cone, contradicted by the clean lower bound. Otherwise a dirty prefix operand allows dead gate 17 to be replaced by a live junk copy without changing the live computation. Dead suffix slots can be filled by junk AND copies, then the prefix can be pruned/padded. This is a target-specific lower-bound argument, not an arbitrary graph or arbitrary-size WLOG.

## Ancestor bounds and suffix restriction

The ancestor flags encode structural transitive dependency, including repeated operands. The partial-edge bound counts the root plus its strict ancestors. For proper support S and accepted residual graph H, its actual constraint is

`|S| + |E(H)| + |cover(H)| <= 2 + number_of_strict_ancestor_gates`.

Moving negative ancestor literals to the left gives precisely the generator's bound `g+2`. Full support remains exempt. The 604 composition controls independently computed ancestor cones and minimum covers, checking 10268 instances of this inequality. The common-neighbor consequence uses productivity: a first descendant AND would require a nonempty opposite support adjacent to every inherited support vertex. Thus no such AND can follow an ancestor support without a common neighbor. Suffix gates are not constrained by this prefix consequence.

The three-suffix-AND cut is valid after all-live normalization. Choose the latest junk AND and an independent input making it true. A live path to the false output must encounter another AND; an OR-only path would propagate TRUE. That later AND is clean by maximality of the chosen junk index. Together with the two junk ANDs, this gives three distinct suffix ANDs. The six pairwise operation clauses say exactly that at most one of the four suffix gates is OR. No one-junk impossibility is used.

## New bounded controls and an adversarial example

The new controls exercise the composition, rather than replaying every old individual-gadget test:

- 600 deterministic random clean-prefix circuits plus four targeted circuits; truth functions are represented on all 2048 inputs.
- 548 full-support deletions, 560 absorbed-OR deletions, 233 unproductive-AND deletions, 21 duplicate deletions, and a targeted dominance deletion. Core sizes 0–11 and 15–17 occur, covering empty-core, single-copy padding, and no-padding endpoints.
- Every retained suffix preserves its nonempty independent-input values, its edge values never decrease, and all final liveness/order/distinctness/productivity/canonicalization checks pass.
- 34 normalized circuits extend to complete assignments satisfying every retained actual CNF clause: 3861992 clause evaluations. Exactly 978 clauses are omitted in these synthetic controls: 970 target-output requirements, the first/second-junk requirements, and six suffix-operation clauses. These samples are not claimed to compute the target. The separate byte reproduction uses the entire unmodified CNF.
- Final run: exit 0, 9.33 seconds, empty stderr. No solver or Lean process was launched.

A concrete counterexample rules out an overstrong proof of dominance, without blocking the actual normalization. Let

`B=x0∧x9`, `C=x2∧x10`, `D=x9∨C`, `g=x0∧D`.

All ANDs are clean; g and B are false on every independent input, and every edge accepted by g is accepted by B. Yet on input `{0,2,10}`, g is TRUE and B is FALSE. Replacing g by B can therefore decrease an intermediate value on a larger positive input. A future Lean proof must use independent-row equality plus edge-row nondecrease, not pointwise equality or pointwise monotone increase. The current review already uses the correct weaker invariant. Similarly, replacing the OR of all eleven inputs by free TRUE changes its empty-input value; final-output monotonicity is essential.

## Evidence files and next direction

All scratch paths below are under `/tmp/oec/pequalnp-pilot-18/orch/S04/`.

- Reproducible control source: `audit_composition.py`, SHA `742d75ca6cde0e8601616dd4d9e9eaefab67eb8bb248275b8f789c40c817be5d`.
- Result and complete final stdout: `composition-result.json`, `composition4.stdout.log`, both SHA `13745e1ce044a791246730732c40571cbafa0d0ac2b766ea2468a0998ca5e8ee`.
- Complete final stderr: `composition4.stderr.log`, empty. Generation log: `recreation.log`. Recreated CNFs and metadata remain in the same owned directory.
- Adversarial scalar check: `semantic-caveats.json`, SHA `b7db36d8fc5990761cc398c28fce01a0ce3d97cd16b29be96a9ca202c49ab3d1`.
- Earlier harness diagnostics are retained as `composition*.stdout.log` and `composition*.stderr.log`. The first two attempts exposed only harness bookkeeping: source-line tagging and arbitrary TRUE defaults for one-way lex flags. Both were corrected before the successful controls.

Read the updated NOTES and S02/S03/S06/S08 reports before this recommendation. There is no completeness reason from this audit to restart the current originalDAG run. S06's checked redundant clauses can be considered with their certificate provenance. The now-compiling 40-row boundary theorem gives a useful basis for future formal normalization: define equality on negative rows and implication on positive edge rows, prove propagation through a fixed monotone suffix, then formalize deletion/prune/pad with its decreasing core count. S02's candidate repairs remain a separate constructive route. Exhausting this shard alone still leaves the global theorem open.

No named proof file, other agent output, worker, lease, credential, remote, or git history was modified. No new Lean fragment is claimed.

## Independent review of S01 consecutive junk: PASS

Additional review requested by the orchestrator at about 03:31 UTC; completed about 03:33 UTC. Reviewed S01 snapshot SHA `26f17ec6c2b3bc13411f42143d3a94b358e627e8fdad64725d9e4742bf4cfbc7`, preserved as `orch/S04/S01-reviewed-snapshot.md`. This verdict covers the main consecutive-junk normalization and its prefix composition. It does not cover S01's additional sorted-chain restrictions or any not-yet-supplied generator/CNF delta.

**The H-clean argument is valid.** In each applicable case the original factorization gives `F = H AND O`, hence `F <= H` pointwise. By definition, clean H is false on every graph-independent input, so `H <= F` pointwise. Thus H=F. Equivalently, if only edge coverage has been recorded, monotonicity takes H from every positive edge to all positive inputs; cleanliness excludes every negative input. Higher-degree terms cannot introduce an exception: any additional accepted input is either positive, where F is already true, or independent, where cleanliness forbids it. No assertion that clean signals have only degree-two terms is needed.

**The prefix-pair contradiction uses exactly the stated clean bound.** When R and T are both prefix wires, `H=R AND T` can be computed by the 17 clean-prefix gates plus one AND. If H is clean and `F=H AND O`, that 18-gate circuit computes F with every AND clean. Propagate free constants and delete aliases without increasing gate count, obtaining an original-model clean circuit, contrary to the lower bound 22. This argument is not applied when one factor is the dirty gate D. In those cases a clean H is instead realized by the retained dirty D, two dirty AND copies, and the clean final AND; there is no illicit appeal to a global clean bound for a dirty circuit.

The reference analysis is exhaustive. In AOAA let D=g17, O=g18, J=g19. Liveness forces J to feed the final AND. If J reads O, write `J=O AND T` and `F=J AND R`. T is prefix, D or O. R cannot be J or O because either would make the output equal the dirty J; thus R is prefix or D. These are all available wires. The cases below preserve the entire output function before prefix normalization.

| Case | Independent check |
|---|---|
| J does not read O | Swapping O/J is topologically valid, preserves all references after remapping, and yields AAOA with junk18. |
| T=O, R=D | If O read D, absorption would make F=D dirty. O therefore uses only prefix wires. D, copy(D), O, copy(D) AND O is live AAOA. |
| T=O, R prefix | D can reach the output only through O, so O=D OR Q. D, copy(D), copy(D) OR Q, R AND that OR is live AAOA; Q=D is allowed. |
| T=D, R prefix | If O reads D, absorb it and use a two-copy D chain before the final R AND D. Otherwise form H=R AND D: dirty H gives D,H,O,H AND O; clean H equals F and gives the same D-copy construction. |
| T prefix, R=D | The preceding case applies with T/R interchanged; no role of a dirty operand is lost. |
| T,R prefix | Liveness forces O to read D. H=R AND T covers F and must be dirty by the 18-clean-gate contradiction. D,H,O,H AND O is live AAOA with junk17 and junk18. |

For AAAA, if gate18 is clean and gate19 dirty, gate19 cannot read gate18 because an AND with a clean operand is clean. Swapping those adjacent gates is therefore valid and gives junk18. In AAOA, gate18 is the only possible second junk. In AAAO, live gate19 is an operand of the clean final OR and must itself be clean, so the second junk again must be gate18. Every constructed suffix contains four gates, is fully live, leaves gate17 dirty, and makes gate18 a dirty AND. Repeated operands and constants cause no omitted port case.

**Prefix composition remains sound.** The suffix rewrites may discard prefix dependencies, so the previously encoded liveness/ancestor variables cannot simply be reused as a Boolean model. Instead prune and normalize the prefix core to a fixed point, then insert the final OR-copy chain as in the earlier audit. Each surviving suffix signal keeps its values on every nonempty independent input, preserving the dirty witnesses at gates17 and18; edge values can only increase. Since the suffix computed F before those prefix steps, the final 40-row values still determine F. Prefix rewrites do not remove suffix-to-suffix edges, so all four suffix gates stay live. The final padding restores their indices and supplies a newly satisfying assignment for exact ancestor flags, cost covers, lex flags and other auxiliaries. No commutation of successive rewrites is assumed.

The safe SAT conclusion is existence of a representative satisfying the additional unit `junk[18]`. It excludes AOAA because junk18 implies AND18. **This unit is a normalization restriction, not an implied clause of the existing originalDAG CNF.** Any checked UNSAT for the new formula must retain the mathematical normalization as part of its interpretation; it cannot be appended to an old RUP/DSR derivation without separately proving a suitable implication. The original solver inputs remain untouched.

The independent bounded control enumerated 259200 syntactic suffix configurations over five independent prefix signals plus FALSE/TRUE, with four representative shapes for D. Of these, 4616 satisfy all-live, junk17, at least two junk ANDs, and the explicit no-clean-prefix-pair-output premise. It checks exact output truth on all 32 assignments, all four suffix gates live, unchanged D, and junk17/junk18 after rewriting. Counts: AAAA2070, AOAA1088, AAOA971, AAAO487. Every listed AOAA branch was exercised, including 126 clean-H collapses and 243 dirty-H cases. These finite controls do not enumerate all possible graph-specific prefix functions; the mathematical argument above supplies that generality.

Evidence in `orch/S04/`: `review_consecutive_junk.py` SHA `2572b8402d419ed6b9fd637bcbe53c64de9b5ca471eaa9e0697e7e449c145c57`; full result with representative before/after gates `consecutive-junk-result.json`; complete logs `consecutive-junk-final.stdout.log` and `consecutive-junk-final.stderr.log` (empty stderr, exit0, under one second). No solver or Lean build was launched. The orchestrator was notified through locked NOTES before this report addition. Next concrete review is the fresh candidate CNF's exact parent-plus-J18 delta and provenance, once supplied.

## Fresh J18 family delta review: PASS

Completed 03:35 UTC, then cross-checked against S01's newly supplied audit at 03:39 UTC. Exact scope: `orch/S01/consecutive-junk-v2/{normalized,AAAA,AAOA,AAAO}`. Generator SHA `3802650c1492cb267a8f8ae5e44715b9b86fe88e642617b85ffbbe857184bb71`; family manifest SHA `fad819eb7f39b301255cb2cedfcadd7d616dd80be15f591b1beea69b4faafb76`.

The normalized file is the original body plus exactly unit3243, with 11968 variables and 114567 clauses. Each operation case is the original body plus unit3243 and its four signed operation units, with 114571 clauses. The operation variables are `[2807,3072,3341,3614]`. All original metadata fields except CNF hash and clause count are preserved. No chain clauses are hidden in the four scoped files.

| File | CNF SHA-256 |
|---|---|
| normalized | `3fefefe3949bc703fc2b9f023be12bc42f1afe7619e8ed5ed63be2f8e7648812` |
| AAAA | `f50627e82144e04dd204302967e5d95b21e7fb6504cf964a35657173eacc3d02` |
| AAOA | `70308894ffc6f4c3b682140c7df3d17ed3035c79dc66f56dc51bd47020004e91` |
| AAAO | `af8cf38d730b3ffaa1245321ce87d3e2dcec43b2a64f180f7962a6f255a4bf29` |

All sixteen Boolean operation assignments were checked: AND17, AND18, and at least three suffix ANDs give exactly these three disjoint cases. Parent-clause preservation is byte exact. Independent review JSON `orch/S04/j18-delta-review.json` SHA `a12ddf32ac70dc5a84f50982bbd7c76b56a6a27b262c937c8ac4cb110c58a599` records all metadata hashes and exact added clauses; complete logs are `j18-delta.stdout.log` / `j18-delta.stderr.log` (empty stderr, exit0). Source `review_j18_delta.py` is retained separately from S01's self-audit. The latter's new source and `encoding-validation.json` agree on all four scoped artifacts.

The metadata's pending-review wording predates this external hash-bound PASS. Keep this review attached rather than treating that wording as a mathematical failure. `AAAA-chain` and `AAAO-chain` remain outside this review. No solver or existing input was modified. Authorized S07 restriction work is reported separately in `S07-restriction.md`.

## Extension at 03:48 UTC: AAAA/AAAO chains PASS

This subsequent review extends the earlier scope to both v2 chain variants. **PASS for the mathematical existence normalizations and exact CNF deltas**, with the degenerate-final-OR repair stated below. No solver or new Lean run was made by S04.

For AAAA, the four live AND gates have at most five external prefix-wire occurrences: among their eight input ports, at least three read suffix gates. Associativity and idempotence express the output as their product. Choose an inclusion-minimal subfamily Q whose product is clean on independent inputs. Removing factors increases the function, while cleanliness bounds the result above by F; hence its product remains exactly F. The empty family is not clean. A one-factor family would give F in the clean prefix, and a two-factor family would add only one clean AND. The clean bound22 excludes both, so 3<=|Q|<=5.

Each retained factor has a private independent witness where all other Q factors are TRUE and it is FALSE. A witness extends to a maximal independent input: the other factors remain TRUE by monotonicity, and the missing factor must remain FALSE because the whole product is clean. Thus the existing 24 negative rows suffice. Distinct retained factors have distinct negative-row functions; no TRUE-like factor is retained.

Sort Q by wire index and repeat its least index until there are five leaf occurrences. The chain's first three AND outputs all omit its greatest retained factor. The same private negative row makes all three outputs TRUE, giving junk17,junk18,junk19. The last output is F. The construction supplies the canonical patterns stated by S01. The implemented inequalities `a<=b<=c<d<e` also admit `a<b=c<d<e`; that additional pattern only weakens the restriction and is safe.

For AAAO, live g19 feeds the final clean OR and is clean. Gate18 must be the second junk AND. Dirty g17/g18 cannot feed the final OR directly, so all three suffix ANDs reach g19 and their branch has at most four external factors. **One omitted case in the original prose needs repair:** the final OR may be `OR(g19,g19)`. Replace this by `OR(FALSE,g19)`, using existing free-FALSE source11. The function and all four suffix gates' liveness are unchanged; the actual chain CNF already permits this value of P. Otherwise the final OR's other operand is directly a clean prefix wire P.

Choose a minimal clean factor subfamily for g19. Its product may be larger than old g19, but remains below F, and `P OR product(Q)` remains F. A one-factor family would yield a clean circuit with at most18 gates; a two-factor family would yield at most19. Hence |Q| is3 or4. Sort it, repeat the least factor if needed, and use the four-factor chain. The private negative witness for its greatest factor makes g17/g18 dirty and g19 clean. P stays clean. This uses only clean22, not a one-junk or arbitrary-circuit22 bound.

**Joint prefix composition:** first prune discarded dependencies and stabilize the prefix core under all reviewed rewrites. Negative functions of every retained factor and P are unchanged; factor minimality and the private witnesses survive. An alias cannot identify two retained Q factors, since their negative functions are distinct. In AAAO it also cannot identify P with a Q factor: P is clean and each Q factor is dirty. If padding is needed, the highest live core gate is a selected factor or P. Attach the final OR-copy chain there and redirect its selected role through the chain endpoint. Then re-sort the retained Q representatives and rebuild the suffix chain, repeating the new least representative as required. Redirect every repeated occurrence of that representative consistently. This preserves padding liveness and avoids claiming that the old sorted occurrence list remains sorted after renumbering. Core lex order and all prefix cuts survive as in the earlier audit; recompute the auxiliary assignments.

The independent exact-delta reconstruction found:

| Case | CNF SHA-256 | Clauses | Added to original |
|---|---|---:|---:|
| AAAA-chain | `41995c72708a950daa154eb3dfa50447b4a4f6ce6199082f14a28a8cfdda1730` |116381|1815|
| AAAO-chain | `a8e94b6cfeaafb8b6c4e01d33e6f552a984e395d224dc3d6281d99cc49850753` |115946|1380|

Both retain11968 variables and every original body byte. Their deltas are J18 plus four operation units, three predecessor-right-port units, six prohibitions on suffix-valued left ports, the signed J19 unit, and the stated sorted-leaf clauses. The latter contribute1800 or1365 clauses. AAAA forces J19; AAAO forces its negation. The final AAAO left port remains an arbitrary prefix source, including FALSE. All source, parent, family and metadata hashes match.

Controls checked6300 leaf-order assignments and1038 factor-permutation/padding configurations on27696 Boolean rows, including padding a factor, padding P and no padding. These controls verify the local normal form; the mathematical argument supplies the general existence implication. Review `orch/S04/chain-review.json` SHA `299f6bdc23ac20e8f9b54cae7eb3a787c1aacf951ab08b8314be212c67f1472d`; source `review_chain_variants.py` SHA `c0059c6e170b5ff5a8c3c55ca82ba5bd8e0148bbccb4e5f5fa972f15a3e15345`; complete logs `chain-review.stdout.log` and `.stderr.log` (empty stderr, exit0). Main received the PASS before launching its new chain run. These remain fresh normalization targets, not implied clauses of the unchanged original CNF.

## Extension at 03:50 UTC: four AAOA forms plus AAAA fallback PASS

**PASS for S01's mathematical coverage and permitted leaf symmetries.** No newly generated AAOA-template CNF is covered by this verdict yet. Four template UNSAT results alone do not exclude every original AAOA circuit: the absorbed cases move to AAAA and require that fallback as well.

Write D=g17, J=g18, O=g19. D/J are dirty ANDs, O is OR, and the final output is `O AND R`. Liveness forces O into the output. R cannot be O: J would reach O through only an OR and make the output dirty. Thus R is a prefix wire, D or J. J either is `D AND C`, with C prefix or D, or is an independent prefix pair.

The following case review covers every available operand, including repeated operands and constants:

| Final R | J shape | Result |
|---|---|---|
| Prefix | D AND C | J must feed O. A prefix other OR operand gives T1. Other operand D or J absorbs the OR and gives the AAAA fallback. If C=D, repeat one prefix factor of D to represent the same product. |
| Prefix | Independent pair | D must be O's other operand, giving T2. |
| D | D AND C | Actually impossible: J<=D and liveness gives J<=O, hence J<=F, contradicting dirty J. S01's extra rewrite branch is harmless but unreachable. |
| D | Independent pair | J must feed O. Other operand D is impossible; J gives an absorbed conjunction/AAAA; a prefix wire gives T3. |
| J | D AND C | O cannot read D or J, since either would make the output J dirty. O has two prefix operands, giving T4, including a repeated factor when J=D. |
| J | Independent pair | D must feed O. Other operand J is impossible; D gives AAAA; a prefix wire gives T3 after swapping the independent dirty pairs into their required outer/inner roles. |

The reviewed schedules are exactly:

| Form | g17 | g18 | g19 | g20 |
|---|---|---|---|---|
| T1: a(b+cde) | c AND d | e AND g17 | b OR g18 | a AND g19 |
| T2: a(bc+de) | b AND c | d AND e | g17 OR g18 | a AND g19 |
| T3: ab(c+de) | a AND b | d AND e | c OR g18 | g17 AND g19 |
| T4: abc(d+e) | a AND b | c AND g17 | d OR e | g18 AND g19 |

For T1/T4 the three-factor product is dirty, so any two-factor subproduct is dirty; sorting that triple preserves both junk gates. For T2 each pair may be sorted and the two OR branches exchanged. For T3 sort the two pairs independently, but do not exchange the outer/inner roles as an extra symmetry. Sort the T4 OR pair freely. Repeated factors are allowed. Every displayed gate has a later reader. Absorption fallbacks are exact pure conjunctions and can use the already reviewed minimal-factor AAAA chain, preserving the junk requirements.

Prune/stabilize/pad remains compatible. Prefix rewrites preserve every leaf's negative values and cannot reduce edge values, so the fixed monotone suffix still computes F on the boundary and retains both junk flags. Redirect a needed leaf through the final prefix copy chain; if the same selected signal occurs several times, use a consistent representative. Rebuild only the template's permitted sorted groups. There is no additional whole-leaf ordering or exchange of T3 roles. All auxiliary flags can be recomputed. Unlike the chain forms, the four AAOA templates may overlap; they form an existence cover together with AAAA, not a disjoint operation partition.

Independent bounded enumeration examined453600 syntactic port configurations over five independent prefix signals plus constants. The5960 cases satisfying all-live, dirty D/J and the necessary no-prefix-pair-output premise all passed exact output equality on32 rows, suffix liveness, dirty17/18 and the approved leaf reorderings. Counts: T1=1260,T2=660,T3=2040,T4=1100,AAAA=900;190720 rows total. The impossible R=D/chained-J branch has no eligible example, as the direct argument predicts. These are algebraic controls, not graph witnesses or exhaustive prefix-function enumeration.

With five distinct terminals, minimal-term-size/intersection signatures are T1=(2,4;1), T2=(3,3;1), T3=(3,4;2), T4=(4,4;3). They are invariant under relabeling and all distinct. Repeating a terminal or using a constant loses a fifth essential variable. Thus removing T3/T4 requires a further graph-specific theorem; generic Boolean rewriting does not suffice.

Review `orch/S04/aaOA-review.json` SHA `43c372c7bf7ce40f262a907323708c182e5e67b58b660ab8ff03922ce4a27b48`; source `review_aaOA_forms.py` SHA `ef6dfe937175278d68c9b8583e14034055d8ae9fa69669fb81ea823bc2da4fdd`; complete logs `aaOA-review.stdout.log` / `.stderr.log` (empty stderr, exit0). Main/S01 were notified through locked NOTES before this report addition. Exact future template deltas require a separate review against these schedules and symmetries.

## Extension at 03:53 UTC: fresh four-AAOA CNF deltas PASS

The subsequently available `orch/S01/aaoa-four-v1/` is now independently reviewed. **PASS** for exact parent preservation, intended topology, permitted symmetry cuts and metadata binding. Source `build_aaoa_shapes.py` SHA `6bcb7e1abdb2c65ffdc9a6a1ced8554509ed2f96a40a756f30d718708256ae63`; family SHA `b05805738736e9b04257657dd8bd39d0fe1c6c31428f191a9fa727fb32109401`. The parent is the reviewed AAOA case SHA `70308894ffc6f4c3b682140c7df3d17ed3035c79dc66f56dc51bd47020004e91`, metadata SHA `0f530e106a5811be95fb87df8802be78bd6a45f91c4ef548acf1d4688c00857f`.

| Case | CNF SHA-256 | Clauses | Added |
|---|---|---:|---:|
| T1 | `422b20c5d9fd5c7eff0ec8a4d7283c70750686da38e3bc3e1dc68e7a1dd5353c` |115450|879|
| T2 | `a295babc305737a921da6bb5c0e990f6c91b2a4c200544d57bcd3abc3e574c3b` |115884|1313|
| T3 | `0ab8fcacbcfe9fa8e094d8db4d0a52eb5d885a032313992ac7c02f312eaffbdf` |115448|877|
| T4 | `661f44876da7e7f8d24d9a06f64ae3708037fc19048e9e20153c47e6a49ea5e3` |115884|1313|

All have11968 variables. Every original AAOA parent clause is byte-preserved; no junk or correctness clause is removed. Fixed selector units implement exactly the table above. Every free terminal port excludes suffix sources. Orders are non-strict: T1/T4's three-factor product is sorted, T4's OR pair is sorted, T3's pairs are independently sorted, and T2 sorts each pair then compares the first leaf of the first pair with the first leaf of the second. The latter is weaker than full lexicographic branch ordering and is justified by the permitted OR-branch exchange. No exchange of T3 outer/inner roles is imposed. Repeated terminals and constants remain available.

Independently reconstructed added clauses match every child byte and each complete `aaoa_added_clauses` field. All inherited metadata fields except hash/count are unchanged. Parent/source/family/CNF/metadata hashes match. Metadata explicitly retains the AAAA fallback requirement and disclaims logical implication of the parent; its pending-review wording predates this external PASS.

In addition to source/delta inspection,1000 canonical selector assignments satisfied1095500 added clauses. Script `orch/S04/review_aaoa_deltas.py` SHA `56fb0f205bbb25fd9d248caed7e13d300636f2dcf8373fac885b571080c5a0e1`; result `aaoa-delta-review.json`; complete logs `aaoa-delta.stdout.log` and `.stderr.log` (empty stderr, exit0, under one second). Main/S01 were notified immediately under the notes lock. No solver or Lean process was started.

The reviewed complete existence cover is now the two chain CNFs plus T1–T4, subject to the documented mathematical normalizations. The four AAOA CNFs by themselves are not an exhaustion of AAOA, and none of these reviews is a solver verdict or a Lean global refutation.

## Joint factor charge: independent mathematical PASS, 04:08 UTC

Reviewed S01's `orch/S01/joint-factor-cost.md`, SHA
`78070f3939d1ac081e67f1b4f18e1655e1aaaed7e4efa4b0d9fa3a4cf24d865f`.
For a minimal family of at least three proper-support full-cover factors in
a productive clean prefix, with distinguished support S and a nonempty
residual graph, the bound is sound:

    m >= |S| + |E(G-S)| + tau(G-S) - 1 + z + d.

Here z counts other factors with no common neighbor, and d counts distinct
owners in S which are the unique common neighbor of another factor's
support. Owners outside S and repeated copies of the same owner receive no
extra charge. This is a mathematical review, not a Lean theorem, implemented
cut, or UNSAT certificate.

Minimality gives incomparable supports because a clean full-cover wire with
proper support T computes exactly F OR OR(T). It also makes each pair dirty:
the pair is a proper subfamily when the family has at least three members.
These two consequences are used at different points and must both survive
any later application to a selected tail family.

If another chosen factor is an ancestor of the distinguished output, choose
the first AND along a path from it. The path up to that AND consists of ORs,
so the entering operand A dominates the chosen factor and accepts every
ambient edge. Productivity and cleanliness force the other operand B to
have a nonempty support contained in the factor's common-neighbor set.
An empty common-neighbor set therefore forbids ancestry. For a unique owner
v, B has support exactly {v}.

If v is in S, set S to zero. On every residual independent input, both B
and A AND B are false; this includes the empty input. On every residual
edge row, A is true, so A AND B equals B. Redirecting this AND's output to
B consequently preserves every downstream wire on all these boundary
rows. It may change larger positive rows, which is harmless: the actual
partial-edge lower bound needs ambient cleanliness, zero output support,
and acceptance of the residual edges. It does not need all intermediate
functions to remain pointwise equal.

Different charged owners give different AND gates. If their paths enter
the same operand of one gate, the other operand's support is contained in
two distinct singleton owner sets, contradicting productivity. If they
enter opposite operands, that AND dominates the conjunction of the two
chosen factors. That conjunction is dirty, contradicting cleanliness.

The overlap concern is resolved by one invariant on the original DAG:
every rewritten wire has its original value on all residual independent
and edge rows. Process gates in topological order, redirecting charged
ANDs to their designated original B operands. Earlier redirections preserve
both operands on the boundary, so the local equality still applies even
when B contains another charged gate. This produces an acyclic circuit and
deletes each charged original node once. If ordinary constant simplification
already deleted a charged node, it has already paid that charge.

Independently mark the pure-S OR nodes and their boundary OR nodes in the
original OR-only ancestry of the distinguished output. Their component
count gives at least |S| distinct OR nodes. Pure-S inputs remain exactly
FALSE after restriction; the marked boundary ORs remain exact aliases of
their other operands. These OR nodes cannot coincide with charged ANDs.
Thus the cone loses at least |S|+t original nodes, even with shared edges,
copies, repeated operands, and constants. FALSE may be included among the
zero sources in the component argument; TRUE cannot enter this OR-only
ancestry because the distinguished support is proper. Eliminate any
remaining constant/alias gates before applying the actual partial-edge
theorem; the nonempty residual guarantees a nonconstant retained output.

Each of the z factors with no common neighbor is outside the cone. Each
owner group without an ancestor representative supplies a distinct output
gate outside it. Minimality excludes raw-input/constant factors and repeated
output nodes; an output cannot represent two distinct unique-owner groups.
These outside gates pay z+d-t. Adding their count to the cone bound proves
the claimed inequality. Dead nodes can only increase m.

For N(1), N(4), N(8), the individual bounds are 16,13,12. Distinguish N(1):
owners4 and8 are distinct and lie in N(1), giving a joint bound18. For
N(3), N(6), N(7), the bounds are17,14,14; owners6 and7 lie in N(3), giving19.
Both triples are minimal (the three triangle singleton inputs are private
witnesses), and their products equal F on all2048 inputs. Thus **all twelve
S02 cases with these exact factors in a17-gate clean productive prefix
can be retired**, regardless of output order or last-three placement. This
does not exclude a larger clean prefix or all possible AAAA factor families.

Independent finite controls are in `orch/S04/review_joint_factor.py`, SHA
`411d45e3f0e0cd6de9e3fe5838ffdad0bdb3346dd4be022ed0eece571c0c10dc`;
results and complete circuits/redirections are in `joint-factor-review.json`.
All4096 triangle product rows, exact residual minimum covers, and eight
ancestor/nonancestor charge cases pass. Eight actual productive clean DAGs
with shared edge gates and overlapping charged cones pass34696 all-wire
boundary comparisons after simultaneous OR/AND deletion. Variants include
repeated OR inputs, FALSE copies, and dead TRUE copies. Full logs are
`joint-factor-review.stdout.log` and `.stderr.log` (empty stderr, exit0).
These controls stress the local proof mechanisms; they are not an exhaustive
enumeration of circuits or a substitute for the mathematical argument.

The original triangle generator delta review was superseded by this
obstruction before any solver launch, following main's direction. Its source
SHA is `e24f9c066ab8a37fa9dbe0d028acb594b8d6d8bc83e9f482fd62e8a390920538`;
its candidate-only status remains. S04 does not claim an independent exact
unit-delta PASS for that retired generator.

Next application: enumerate minimal support families using the joint bound,
then independently review the enumeration's coverage. A later AAAA cut must
either retain this minimal-family witness normalization or explicitly encode
the needed antichain and dirty-pair hypotheses. The joint inequality is not
automatically a logical consequence for every redundant family permitted
by the weaker chain encoding. No active CNF was changed.

## Preservation and independent finite-family follow-up, 04:15 UTC

The six normal forms and joint-cost proof/reviews are preserved in
`orch/S04/normalization-preservation-v1.tar.gz`, SHA
`ab76bf72819cac52f98c13d133b94fceedc2dc7fa4952ef06f825d19081beea4`,
735815bytes. It has164 regular members, zero raw CNFs, all mathematical/source
and exact-delta reviews, full logs, exact metadata, and a portable Python
recipe. Running the unchanged archived generators reproduced all14 CNFs,
all14 metadata files, and both family manifests byte for byte. The archive's
manifest SHA is `cb20dfacd44f6d62ebb3ea77773ce7b6b2237cfcb2ea078b072f4a4a18243a05`;
`normalization-preservation-validation.json` records all checks. Main was
notified under the notes lock. This archive is immutable; the following newer
enumeration review is a separate addendum.

S01's `enumerate_joint_supports.py` SHA
`1fa83032ddea490b4c7909362d9bd3e3b7b40e99f306cafc20845c2a220567a0`
reports a survivor, not exhaustion. Independent review PASS: its family is

    A = F OR x8 OR x10
    B = F OR x9 OR x10
    C = F OR x4 OR x6.

Their individual bounds are14,14,16 and joint bounds15,15,17. Unique common
neighbors are4,0,10, respectively. All2048 scalar input rows satisfy ABC=F.
Private maximal independent witnesses, indexed in the established bitmask
convention, are540 for A,325 for B, and1066 for C. Thus the family is minimal
and passes the reviewed joint-cost support relaxation. It is not an actual
shared17-gate prefix or a21-gate circuit.

The source's candidate pool excludes full support, supports whose individual
cost exceeds17, and supports with no zero maximal independent row. All are
safe exclusions for a minimal family. Independent exact vertex-cover
calculation recovers958 candidates,49 with a common neighbor. Its handling
of edgeless residuals deliberately omits the new joint charge, which only
weakens the filter. Empty/singleton supports are already excluded by the
individual bound. Every remaining individual bound is at least6; the filler
cost6 in the partial sorted-slot check is therefore safe.

The pruning argument is sound. Increasing selected owners only increases
the joint charge; each owner's bit is counted once. Including a factor's
own unique owner in the accumulated owner set adds nothing because that
owner is not in its support in a loopless graph. The count of other
empty-common-neighbor factors is r minus its own indicator. Sorted individual
costs must fit the last k distinct gate slots. Equal/comparable zero sets
cannot belong to a minimal complete cover; a factor losing all private
maximal-independent rows can never regain them when more factors are added.
The chosen-uncovered-row branching assigns each covering family to its first
selected candidate for that row; excluding earlier candidates in later
branches does not lose a family. A partial cover of all rows cannot be
extended to a larger minimal family. Time-limit status is explicitly UNKNOWN.

An independent brute-force traversal of all18424 unordered triples from
the49 common-neighbor candidates finds **515** minimal support families
passing individual, sorted-slot, and joint bounds. The complete finite list
is retained in `orch/S04/joint-enumeration-review.json`. This traversal is
complete only for k=3,r=0 and only for this support relaxation. It confirms
that the current joint inequality alone cannot exhaust the AAAA case.

There is a useful further necessary condition for S01's reported survivor.
In any17-gate productive clean prefix producing A,B,C, B must be an ancestor
of C. Indeed C has individual lower bound16, and A's owner4 lies in C's
support: A costs one gate whether inside C's cone (charged AND) or outside
(its distinct output gate). If B is also outside, total cost is at least18.
If A is inside, C's cone contains all17 gates; if A is outside, C's cone has
exactly16 gates and A is the sole outside gate. The first AND along the
mandatory B-to-C path has other-operand support {0}. Owner0 lies outside
C's support, precisely the interaction uncharged by the current inequality.
This is a concrete next structural target; no stronger deletion charge is
claimed without a new proof.

Independent source `orch/S04/review_joint_enumeration.py` SHA
`132e6055ae70e65929d62513b091f32f34550d373d81b6b380a4b4796765f389`;
full stdout/stderr are `joint-enumeration-review.stdout.log` and `.stderr.log`
(empty stderr, exit0,0.12s). No other agent's script was executed or modified,
and no solver, Lean build, worker, lease, or git write was used.

## Tight-survivor obstruction: mathematical PASS and shorter proof

S01's `orch/S01/tight-survivor-obstruction.md`, SHA
`69bb5f1587acceb0fd5ecebf3ed4a525919c439eef62c70a7c11e9ae149a1acc`,
passes independent review. Its `joint-cost-handoff.json` SHA
`d187d5ef0337b54dfcd25bf2722851604463f382e9fad5ca30943b56e41cf328`
binds18 artifacts; every size and hash matches. This proof excludes the
specific full-cover support triple1280,1536,80 from a productive clean
prefix of at most17 gates, with arbitrary output positions. Main/S01 were
notified immediately to retire the candidate pins before any solver launch.

The new arbitrary-ancestor charge is sound. Let W be a full-cover wire of
proper support S, with a nonempty residual graph. Let an ancestor signal R
have nonempty support T not contained in S, with every common neighbor of
T in S. On a path from R to W, the first AND has an entering operand U
containing R through ORs. Its other operand V has a nonempty support inside
the common-neighbor set of T, hence inside S. After setting S to zero, V
and that clean AND both vanish on every independent residual input. Replacing
the AND by V preserves all those negative values and pointwise increases
all restricted downstream values. Every residual edge accepted by W remains
accepted; every retained AND remains clean. This uses nondecrease on edges,
not the stronger equality from the full-cover-ancestor argument.

The original pure-S OR nodes still become FALSE, and their boundary OR
nodes still become exact aliases. They supply at least |S| deleted original
OR nodes, separately from the newly deleted AND. Even if simplification
already removed the AND, that distinct original node has paid its charge.
Free FALSE, copies, and repeated operands do not reduce the deletion count.
The residual output is nonzero with empty support, so constants can be
eliminated before the actual-circuit lower bound is applied. Consequently
the cone of W has at least L(S)+1 gates. R need not cover any target edge.

Here is a shorter complete contradiction for the triple, which avoids the
last two sections of S01's longer argument. Write A,B,C for the full-cover
wires of supports {8,10},{9,10},{4,6}, with individual bounds14,14,16.
The earlier reviewed joint charge forces B to be an ancestor of C: A costs
one extra gate either inside C's cone or outside, so an outside B would
raise the total from16 to18.

All three chosen outputs are distinct OR gates at indices at least13,13,15.
Their supports are incomparable. The B-to-C path therefore needs an AND q,
and A,B,C,q fill all four late positions13 through16. No other late gate
exists. A cannot be an OR intermediate on either side of q: its support
neither contains B's support nor is contained in C's. Thus the path is
direct at both ends:

    q = B AND R,       C = q OR P,       support(P) = {4,6}.

A is not an ancestor of B. If earlier, an A-to-B path would need an AND;
the sole late AND q is later than B. C and q are also later than B. Hence
B's cone is contained in gates0–12 together with B itself. Its lower bound14
forces exact equality: every one of gates0–12 is in B's cone.

P has support {4,6}, so it is neither a raw input nor either free constant.
It cannot be A,B,C,q by their supports and topological order. Therefore P
is a gate among0–12, and hence an ancestor of B. Now

    commonNeighbors({4,6}) = {10} subset {9,10},
    {4,6} is not a subset of {9,10}.

Apply the new arbitrary-ancestor charge directly to R=P and W=B. It forces
B's cone to contain at least L({9,10})+1=15 gates, contradicting its exact14.
This completes the18-gate lower bound without assuming R=x0, without any
absorption rewrite, and without the partial-support cost of P.

For completeness, the longer argument also checks out. If R is computed
among0–12, its support {0} and N(0)={9,10} trigger the same extra charge, so
R must be raw x0. Then P must accept the eight stated residual edges, which
have the displayed disjoint matching4 and vertex cover4, giving cost13.
P must be gate12 and feed the OR B directly, contradicting support
containment. There are exactly four possible late schedules; this argument
also covers C at15 with A at16, and B at14 with A at13. Copies and constants
are excluded by the same support/count statements, not by an implicit
minimal-circuit assumption. Padding a shorter circuit with dead OR gates
does not change the hypotheses or avoid the contradiction.

Independent controls in `orch/S04/review_tight_survivor.py`, SHA
`437a6441a10c31fe45d9e46b864cb46c1da8b68f226471104371e09daec12422`,
verify the18 handoff bindings, four schedules, matching/cover arithmetic,
and eight concrete clean productive DAGs using a non-full-cover ancestor.
The rewritten circuits preserve16192 independent wire values and satisfy
94208 pointwise wire nondecreases. Each control deliberately includes a
strict residual edge-value increase, confirming that equality is not the
invariant required by the new lemma. Full circuits, redirects, results and
stdout/stderr are retained in `tight-survivor-review.json` and corresponding
logs; final exit0, empty stderr,0.37s. The original control version and its
complete logs are retained separately after removal of an irrelevant
tautological assertion; the final source hash above is authoritative.

This is a mathematical prefix obstruction, not a Lean proof or CNF UNSAT
certificate. It rules out this one support family; the other514 triples
in the earlier k=3,r=0 relaxation have not been excluded by this argument.
No active CNF, solver, worker, named proof, or previously handed-off archive
was changed.

## Irrelevant raw-input charge: mathematical and encoding-specification PASS

Reviewed S01 `orch/S01/irrelevant-input-charge.md`, SHA
`951fd0d38db513a2fcfa98ddad5ef9c9dbc8c5d58acc4ba37867d0bc564af48f`.
The claimed one-bit strengthening is sound for every proper-support wire W
in a productive ambient-clean prefix, including partial and empty accepted
residual edge sets. If raw input v is a syntactic ancestor of W, v is outside
its singleton support S, and N_G(v) is contained in S, then

    M >= |S| + |E(H)| + tau(H),

where M counts actual gate ancestors, including W when W is a gate, and H
may be any subset of ambient edges accepted by W outside S. C4-freeness is
required for the existing partial-edge lower bound. The new charge is one
Boolean penalty, not a sum over every qualifying raw input.

Because v is absent from S, its path to W meets an AND. At the first one,
the entering operand contains v in singleton support. Cleanliness makes
the other operand's support a subset of N_G(v), and productivity makes it
nonempty. Setting S to zero makes this operand and the original AND false
on every independent residual input, including the empty input. Bypassing
the AND by that operand preserves these negative values at every retained
wire. It pointwise increases all downstream restricted values, so all H
edge rows remain accepted. This preserves cleanliness for the ambient
induced graph G-S. Intermediate ANDs need not be clean for the smaller
selected graph H; that is exactly why the actual partial-edge theorem,
rather than an exact-output theorem for H, is used.

For nonempty H, the restricted output is nonzero. The pure-S OR component
argument deletes at least |S| original OR gates, separately from the bypassed
AND. Their pure inputs still become exactly FALSE; their boundary ORs remain
exact aliases after the AND replacement. The partial-edge theorem applies
to at most M-|S|-1 remaining gates and gives the stated bound. Higher-degree
positive values may change, and neither W nor its restriction needs to equal
the graph function of H.

For empty H and |S|>=1, no deletion argument is required: the OR-only
ancestry of W must connect all |S| distinct raw support inputs and therefore
contains at least |S|-1 OR nodes. The first AND on v's path is a distinct
additional node, so M>=|S|. This remains true when the output accepts
higher-degree positive inputs but no residual edge rows. For empty S the
asserted inequality is merely M>=0. Moreover, its trigger would require an
isolated v, whose path cannot meet a productive clean AND; this confirms
that no exceptional hidden circuit is needed. Full support cannot trigger
because v must be absent. Free TRUE therefore remains exempt. FALSE, OR
aliases, repeated operands and dead nodes do not reduce the original-node
count. A raw output has no such other-input path; constant outputs do not
supply a counterexample.

The proposed trigger clauses have the correct polarity. For root g, gate
h<=g, and raw vertex v, each side contributes

    p_g OR S_g[v] OR (OR over u in N(v) of NOT S_g[u])
        OR NOT ancestor(g,h) OR NOT selected_side(h,v).

For h=g, omit the ancestor literal, since the stored table contains only
strict ancestors. Every syntactic raw-input path has a first gate reading
that input, so these clauses detect every genuine trigger. Conversely an
ancestor gate selecting raw v supplies that path. Existing ancestry flags
are exact equivalences in the pinned source. Singleton support alone must
not replace syntactic reachability. There are2*11*153=3366 trigger clauses.

No equivalence for p_g is needed. To extend an actual circuit, choose p_g
to indicate whether any trigger holds, choose minimum residual covers, and
assign exact counter thresholds. Off-trigger choose p_g false, including at
full support. An arbitrary true off-trigger choice may fail the strengthened
cost constraint, but its false choice remains available. Thus this is an
existential auxiliary extension argument; it does not assert that every old
nonminimum cover assignment satisfies the strengthened clauses or claim a
RUP proof from the previous CNF.

There is a cheaper implementation specification than rebuilding counters.
In the pinned parent38d93...ace08, the signed counter for root g counts

    weight = popcount(S) + popcount(residual-edge flags)
             + popcount(cover flags) + popcount(NOT strict-ancestor flags).

The original proper-support constraint is weight<=g+2, equivalent to
|S|+|H|+|cover|<=M+1. The root overflow flag represents weight>=g+3. The
preceding root threshold represents weight>=g+2 and, in this exact generator,
has ID `overflow_flag-1`. Therefore append just

    NOT p_g OR NOT (overflow_flag-1)

to enforce weight+p_g<=g+2 on proper support. With p_g=false, full support
retains the original exemption. The total becomes **17 new variables and
3383 added clauses**, consisting of3366 triggers and17 counter links, with
no fresh counter auxiliaries. For unchanged11968-variable parents, the new
penalty IDs are11969..11985. All six reviewed normal forms retain these
original counter blocks, but each production source/delta must still be
checked separately. The numeric ID shortcut must not be assumed for a
different counter implementation or unpinned parent.

Independent source `orch/S04/review_irrelevant_input.py`, SHA
`4fa439ce59425cca9f0a8d2da0a34eac523b6528353885527c5060118fabc7bb`,
reconstructed all17 exact original counter clause blocks and verified their
threshold IDs. Its799 exact counter assignments satisfy1043861 network
clause evaluations. All360448 Boolean trigger/diagonal checks pass. Twenty-four
actual clean productive partial-output DAGs pass72 chosen-H cost checks;
eight have no accepted residual edge, and variants include constant/copy
nodes. Replacement checks preserve every independent wire value and only
increase restricted values. Complete circuits, expected trigger-clause
fixture, counter-link IDs and diagnostics are in `irrelevant-input-review.json`
and its full stdout/stderr logs (exit0, empty stderr,0.90s).

Verdict: mathematical bound, trigger specification and pinned-counter reuse
PASS. No production generator or child CNF has yet received an implementation
PASS from this review. No solver, Lean build, active search, or named proof
was changed. Main/S01 were notified under the notes lock before packaging.

## Generalized three-factor classification: independent PASS

S01 handoff `three-factor-classification-handoff.json`, SHA
`9a48bf0acf8e5aca20a6bda737506b33897e13841f9b5577aee06188822c3f7e`,
binds11 math/source/result/log artifacts. Every binding matches. The generic
proof and finite classification pass independent review:233 exclusions from
the one-spare-AND pattern,199 from the position filter, with20 new exclusions,
give253 excluded and262 remaining among the supplied515 families.

The review concerns three proper full-cover outputs whose conjunction is F
and whose family is minimal, in a productive clean prefix of at most17 gates.
All515 families have distinct incomparable supports, dirty pair products,
and a unique common-neighbor owner for each factor. Their supports have
nonempty residual graphs, as independently checked. In this concrete graph,
a common-neighbor support has size at most4, whereas a vertex cover needs7;
thus the nonempty-residual requirement for the earlier owner charge holds.

When all three individual costs are at least14, their distinct OR outputs
occupy three of positions13–16. If none is ancestral to another, each cone
excludes the other two output gates and has at most15 gates. Otherwise an
incomparable-support ancestry path needs an AND, so the single remaining
late gate q must be that AND. Every selected-output ancestry path uses q.
Two selected factors cannot enter its opposite operands because their pair
is dirty. If both enter the same operand, their paths need a separate OR
merge, unavailable in these four late positions; another selected output
cannot perform that merge because its support is incomparable. Hence there
is one source B and one or two children, covering all nine possible stars.

For every such star q=B AND R and each child C=q OR P_C. The input R has
singleton support equal to B's unique owner, and P_C has support S_C. Both
operands lie in the thirteen earlier gates or raw sources; P_C cannot be
raw or constant because its support has at least two vertices. Source B
and any nonchild exclude q and both other selected outputs, so their cone
capacity is14. Since their costs are at least14, they attain that capacity
and contain every gate0–12. Each child contains this entire source cone,
q and itself, giving exactly16 ancestor gates, with the other selected
output excluded.

The four substantive star restrictions therefore follow. A child pays an
extra deletion if B's owner lies in its support. Its operand P_C, already
an ancestor of B, would instead raise B's tight14-gate cost if the child's
owner lies in S_B. If S_B equals the entire neighborhood of its owner,
a computed R would similarly raise B's cost, forcing R to be that raw input.
Then P_C must cover all target edges not incident to that input. Its partial
support cost must be at most12: a bound13 forces it to gate12, which must
feed B's OR directly and would violate support containment. With two
children, two distinct P_C operands each costing at least12 would force
one to gate12 and give the same contradiction. None of these arguments
assumes a tree, strict operands, or ancestry-free chosen outputs. Families
with minimum cost below14 remain untouched by this star proof.

The separate position filter enumerates every allowed output-position tuple
and every relation on the three temporally ordered output pairs. Its
transitivity and intervening-AND conditions are necessary. When both other
outputs are ancestors of one output, two unselected gates are necessary:
a comparable pair requires successive AND transitions; an incomparable
pair needs distinct first ANDs or an OR merge followed by a shared first
AND. Opposite entry into the same first AND is excluded by pair dirtiness.

For root i, subtracting earlier nonancestor selected outputs from p_i+1
is a valid cone upper bound. If another pair a->b lies earlier but a is
not ancestral to i, its first AND is also outside i's cone; otherwise a
would be ancestral to i. This extra node is distinct from selected outputs
because they are ORs. With only three selected outputs this adds at most
one extra subtraction.

The corresponding cone lower bound uses the individual cost plus the
maximum of two charges: the number of distinct ancestral owners lying in
S_i, and the single irrelevant-raw-input bit. Their deleted ANDs may overlap,
so adding the two charges would be unjustified. The raw essentiality test
is exact: for H_S=F OR OR(S), vertex v is essential iff v belongs to S or
has a neighbor outside S. A singleton witnesses the first alternative;
a residual edge witnesses the second. If neither holds, every edge term
involving v is absorbed by OR(S). An essential input must be a syntactic
ancestor in any implementation, so selected ancestry propagates that raw
input into the later cone. This justifies use of the independently reviewed
irrelevant-input charge. All remaining witness inequalities were checked.

Independent script `orch/S04/review_three_factor_classification.py`, SHA
`8cb412c03bbec35752d2ca8ee47a9ce396fd0dcdf2382cad16ecb15f8847ba9f`,
recomputes individual/partial costs with exact covers, all nine star choices,
and every temporal position/relation assignment. Its traversal differs from
S01's and does not stop after finding a witness. It checks57560 assignments,
finds9007 abstract feasible models, and reproduces every one of the515 family
decisions. All saved position witnesses and their cone bounds agree. The
1545 pair functions were independently checked on full truth-table bitsets.
Full per-family records and complete logs are in
`three-factor-classification-review.json` and its stdout/stderr files
(exit0, empty stderr,0.27s). S01's13927 assignment count reflects its early
exit on each surviving family, not an exhaustive count of all models.

One nonblocking metadata qualification: `pair_features.pure_singleton_OR`
means that the pair is F OR OR(the support intersection), not that it is
just the standalone linear OR. For example the previously reviewed pair
with supports {8,10} and {9,10} equals F OR x10 and remains true on edge(1,4).
This field is unused by the exclusion filters; all supplied flags match the
former interpretation. Future algebra must retain F.

Future cuts may forbid the exact253 excluded support triples when all three
wires are proper full-cover outputs in the17-gate productive clean prefix,
with all output placements covered. The finite tables already certify each
listed triple's minimality and owners. A generic predicate implementation
must retain the corresponding hypotheses, use actual ancestry and signed
costs, and avoid double-counting the owner/raw charges. Arbitrary non-full-
cover wires with the same singleton supports are not covered. Neither a
last-three placement restriction nor a general selected-output antichain
was proved. A generated cut requires its own clause/projection review.

This result does not cover r>0, four/five-factor families, larger or dirty
prefixes, or a whole AAAA exhaustion. The262 retained entries are abstract
necessary-condition witnesses, not shared-prefix constructions. The proposed
separate +2 deletion extension is outside this review. No solver, Lean build,
production CNF, active worker, named proof, or other agent output was changed.

## Disjoint and hitting-number charges: independent mathematical PASS

Reviewed S01's disjoint proof SHA
`29b58a47659e054062fe81a2c98b3a0832fe8bf8feb00d31d3a3071b5f87d475`
and hitting proof SHA
`f0af499ec1028b8093ec953d6654d286f20c9ddd035b19fbb485ad0b9ecb2ae6`.
The six-file disjoint handoff is
`c4ec0d309a0a8c7702629d51ab617138f59c5d663d4e80e972cd17cd7573582c`.
Both pass, with the proper-support, productive, ambient-clean hypotheses
of the earlier partial-edge theorem retained. If I consists of actual raw
ancestors v outside singleton support S with N(v) contained in S, and eta(I)
is the minimum size of a set meeting every N(v), then

    M >= |S| + |E(H)| + cover(H) - 1 + eta(I).

Here M counts the exact gate ancestor cone, including the output; H can be
any chosen accepted ambient edge set disjoint from S. It need not be the
whole residual graph. Pairwise-disjoint neighborhoods give eta(I)=|I|.

Each chosen raw path has a first AND because v is absent from S. All inputs
in I are independent. Inputs assigned to the same first AND enter the same
operand: entering opposite operands would make that clean AND true on an
independent pair. Its other operand has nonempty singleton support, by
productivity, contained in every assigned N(v), by cleanliness. Choosing one
vertex from each such other support hits all neighborhoods. Thus at least
eta(I) distinct original AND nodes are identified; sharing a first AND is
permitted and counted only once. For disjoint neighborhoods the same argument
forces distinct first ANDs individually.

After restricting S to zero, bypass those original ANDs in topological order
by their designated other operands. Every retained independent-input value
is unchanged, because the designated operand has support contained in S;
all other restricted values can only increase. This invariant applies also
when charged cones overlap or a designated operand contains an earlier
charged node. A named gate already pruned is already a deletion, never a
second charge. These AND deletions are disjoint from the support-OR deletions.
For nonempty H the earlier reduction supplies |S| OR deletions and applies
the ambient-clean partial-edge theorem to the remainder. For empty H and
nonempty S, |S|-1 OR support nodes plus the charged ANDs prove the bound
directly. For empty S the AND count is already stronger than the displayed
bound; in this concrete minimum-degree-two graph no nonempty I then exists.
Constants and copy ORs do not invalidate the counts. Full support remains
outside the proper-support theorem and cannot have a genuine input witness.

The independent disjoint review is
`multi-irrelevant-review.json`, SHA
`8c299b8b5a9128d1e9e740606adaf180d42aa157917bcb81b270d7536335b3b1`;
source `review_multi_irrelevant.py`, SHA
`2d243d222f6393534ad782fe90800117b34989547af4fda4f2ef74e27b7bb88a`.
It verifies all six source bindings, all2048 support rows,14 eligible pairs,
three triples,202 potentially +2 supports (132 with residual edges),nine
potentially +3 supports, and6392 threshold-arithmetic cases. Its51 actual
clean DAG controls include overlapping cones, constants, repeated operands,
and empty/partial/full chosen residual edge sets. They preserve30256 negative
wire values, satisfy64256 pointwise nondecreases, and include192 strict edge
gains. A shared-first-AND overlapping-neighborhood control explains why raw
input count alone is not the distinct-deletion count.

The independent hitting review is `hitting-charge-review.json`, SHA
`e4df03fa7c9077847bf16e2850b67b0a0331b79559dd0ca718829c3cb8b50609`;
source `review_hitting_charge.py`, SHA
`32b0c9797728a77ef37dc14ec93f0c8c7db2e9367b65251ef78d1e3365158138`.
An owner-cover dynamic program independently reproduces all125 hitting
numbers and canonical minimum witnesses. All680 input partitions are checked;
379 admit owners and their minimum group counts equal eta. Every2048 support
row and9512 actual-input-subset threshold tests agree. There are24 minimal
+2 triggers (14 pairs,10 triples) and five minimal +3 triggers (three triples,
two quartets). Potential coverage is224 supports for +2,11 for +3,143 for +2
with residual edges, and24 strict improvements over disjoint packing. This
counts possible input witnesses, not established circuit ancestry.

The12 additional overlapping-neighborhood trigger patterns have24 actual
DAG controls with shared first ANDs within groups and overlapping group
cones. They preserve7384 negative wire values, satisfy10192 pointwise
nondecreases, and include40 strict edge gains. Full circuits, restrictions,
bypass maps, scalar results, sources, and complete stdout/stderr are retained
in the review artifacts. Both bounded review scripts exit0 with empty stderr;
these controls support the proof review and are not circuit exhaustion.

The unimplemented hitting outline also passes: beyond the existing +1 cut,
187 input-witness bits and34 rank bits give221 variables. The3366 input
triggers,408 rank-two triggers,85 rank-three triggers and34 unconditional
counter links give3893 clauses;11 full-support guards per link give4233.
For gate g and rank k, use threshold `overflow-k` only when g+2-k is
nonnegative. Gate0/rank3 instead requires a negative rank-bit unit (or its
proper-support guarded version). The implications impose separate ranks;
never sum the +1,+2,+3 flags as a penalty of six. Exact genuine witness bits,
minimum covers and exact threshold assignments establish existential
completeness. No claim that every old auxiliary assignment extends, or that
these mathematical cuts are RUP consequences, is made. An actual generator
and emitted CNF require a separate delta review.

No stronger bound on the262 remaining common-neighbor families follows.
If S has common neighbor u and v outside S has N(v) contained in S, then
N(v) is contained in S contained in N(u). Minimum degree two and C4-freeness
force v=u and S=N(u), so there is at most one such v. A no-common-neighbor
wire cannot reach such a factor through a productive AND; an OR-only path
would preserve its support and also contradict the factor's common neighbor.
Thus no wire in the union of those factor ancestor cones admits +2. This
statement does not concern unrelated prefix outputs outside that union.
The charge may strengthen broader cases; search speed or success is unknown.
This is mathematical/finite/specification PASS only, with no Lean theorem,
global lower-bound conclusion, accepted generated cut, or solver run here.

## Four/five common-neighbor factors: mathematical and finite PASS

S01's27-artifact `five-factor-closure-handoff.json`, SHA
`c0dbd623da51cb86717098177a867eabe3399fc1880d3fe8659a44e4152073b1`,
passes independent source binding, mathematics and finite coverage review.
This concerns minimal families of four/five distinct proper full-cover
outputs of a17-gate productive ambient-clean prefix, with a common neighbor
for every selected support. It supplies no result for r>0, meaning families
containing a support with no common neighbor. The three-factor remainder
stays262; the four-factor remainder becomes115 abstract support patterns.

The five-factor two-spare argument, SHA
`18f85d2797a8d83bbde12d9d7a1d8ba5413db30d835f1b75b497379e2336fa24`,
passes. Every candidate has cost at least11, so five selected OR outputs
occupy five of positions10..16. Only two unselected gates remain there.
For r selected ancestors of another selected output W, follow chosen paths
to their first ANDs. Incomparable supports prevent another selected OR from
being an intermediate OR-only node. OR nodes merge at most two source
components; a first AND cannot accept two unmerged selected components on
opposite operands, because every selected pair product is dirty. Thus OR
merges plus distinct first-AND boundaries number at least r. This counts
actual nodes once and remains valid with fan-out, shared paths and ancestry
among selected sources: an earlier AND ends that source's OR component.
Consequently r<=2, and every selected cone has at most10 core gates, two
spares, its own output, and two selected ancestors: at most15 gates.

For the five remaining maximum-cost15 families with distinct owners and a
unique cost11 factor, the stronger contradiction also passes. A cost15
cone requires two selected ancestors. One spare AND plus one spare OR
cannot carry them: opposite operands are dirty, while same-side merging
would force the other productive operand into the intersection of their
distinct singleton owner sets. Thus both spare gates must be ANDs carrying
selected ancestry. Neither can be spent before all selected sources. The
earliest selected output A consequently has no spare ancestor, has cost11,
and uses all ten core gates. The first spare must descend from A; the second
must also carry a selected ancestor and hence is downstream of A, directly
or via an intervening selected output using the first spare.

Every other selected C has cost>11 and therefore uses a spare AND. Its OR
must be q OR P_C: two clean AND operands have empty support, and another
selected output as operand would violate support incomparability. P_C has
support S_C, so it is a core gate rather than a raw input or constant, since
the candidate supports have size at least two. All core gates are ancestors
of A. If C's unique owner lies in S_A, the reviewed arbitrary-supported-
ancestor charge applied to P_C raises A's lower bound from11 to12, a
contradiction. This proof permits shared core gates, copy operands, and
constants; it never assumes that the selected outputs form an antichain.

The generalized one-spare argument is also valid. For k factors all with
L>=17-k, the last k+1 positions have at most one spare. Ancestry is either
absent, giving cone upper bound18-k, or a star through that spare AND.
Source and nonchildren have exact17-k cones containing all16-k core gates;
children have19-k cones. The earlier owner and raw-operand charges apply.
When the source support is its owner's full neighborhood, distinct partial
child operands must fit before the last core gate. Their sorted cost
capacities are16-k-j through15-k for j children. The independent reviewer
checked these allocations through explicit distinct-position assignments.

The general position proof, SHA
`0e96d0c0804148f390a9b474e36be3219f18f70968fcdc1e7dd5eecdbc91f436`,
and its additional cone inequalities pass. An ancestry chain of ell earlier
selected outputs excluded from W supplies ell-1 distinct excluded ANDs in
disjoint chronological intervals. For an antichain of r selected ancestors,
their cone union contains at least max(M_j)+r-1 gates. At least r further
OR/first-AND boundary nodes lie outside the entire union: each descends from
a selected source and cannot be ancestral to another antichain member.
Adding W gives M_W>=max(M_j)+2*r. For one ancestor the corresponding bound
is M_W>=M_j+2. Propagating these lower bounds is sound. The owner and raw
input charges are combined by maximum, not sum, to avoid overlapping AND
deletions. These are necessary conditions on actual ancestry relations,
not assertions that abstract surviving patterns are circuits.

Independent source `review_four_five.py`, SHA
`6635dbae88e2fccb23ae6bb5754c0d86cc4cfb5ea16f98ccb4a13b2e2b41f4d9`,
uses an edge-branching cover recurrence, independently derives all49 eligible
supports from all2047 proper masks, and verifies the full211876 four-factor
and1906884 five-factor combination censuses. Every slot, minimality, joint
cost, and one-spare decision matches. The known k3 counts515/233 serve as a
control. The four-factor joint-feasible1502 reduce by1190 one-spare exclusions
to312; the five-factor331 reduce by290 to41. All2348 stored joint-feasible
families are bound and checked.

The position review independently generates the40/357 transitive relations
from edge subsets and reverses position traversal. It checks1112320 choices,
validates every supplied surviving witness, and reproduces all197 additional
k4 exclusions, leaving115, and40 additional k5 exclusions, leaving one.
The bespoke five-factor argument independently excludes330/331, also leaving
one, but the two single survivors are DIFFERENT:

- The position filter leaves supports417,562,772,584,1152 with costs11,12,13,
  14,15; the unique-cost11/reverse-owner argument excludes it.
- The bespoke argument leaves417,560,1282,84,1160 with costs11,13,13,14,14;
  the position filter excludes it.

Thus their exclusion union covers all331 k5/r0 joint-feasible families:
290 one-spare,40 position, and one reverse-owner exclusion; zero remain.
Every other support family fails an earlier independently checked necessary
pool, position-capacity, minimality or joint-cost condition. This is a finite
mathematical exclusion of the stated support-family class.

Review result `four-five-review.json`, SHA
`5f7b5661a938c9c05c21cae52644a0beb139484526e695aebe32be2029ff16a7`,
records all source hashes, per-family decisions, witnesses and closure counts.
Final review exits0 in6.64s with empty stderr. The first review harness
incorrectly asserted equality of the two sole survivors after successfully
checking all individual families. Its source and full diagnostics are
preserved as `review_four_five.initial.py` and `four-five-initial.*.log`.
The correction checks the exclusion union explicitly; producer files were
unchanged. This was a reviewer aggregation error, not a producer proof error.

For an AAAA five-leaf representation whose minimal retained factors all have
common neighbors, the result permits an existence normalization to at most
four distinct minimal factors, followed by the already reviewed repeated-leaf
padding and prefix normalization. It does not justify forbidding every
nonminimal original five-leaf representation without that normalization.
An implemented cut or changed generator requires a separate projection/delta
review. No r>0 family, whole AAAA/shard, Lean theorem, or global21-gate lower
bound is concluded. No solver, Lean build or production file was changed.

## New no-common-neighbor region obstruction

Own derivation `orch/S04/no-common-neighbor/no-common-regions.md`, SHA
`3f659429b0dd706d4c3099dc33bdfc8f8b15914cf43b8fa0de50e47adbbf203d`,
supplies a stronger joint lower bound. S01's initial review of the precise
description agreed; full source/control review was requested separately.
This is a new mathematical derivation, not a Lean theorem or generated cut.

A wire whose singleton support has no common neighbor can have only OR
descendants in a productive clean prefix. A first AND would require a
nonempty other support contained in that empty common-neighbor set. Thus
its support is contained in every descendant support, and incomparability
prevents its being an ancestor of another selected minimal full-cover factor.

Let gamma(S) be the minimum number of open graph neighborhoods covering S.
For a proper no-common-neighbor output, its region of no-common-neighbor
gate ancestors consists of t OR gates with at most t+1 boundary occurrences.
Each boundary wire has support in a single neighborhood; the boundary
supports cover S. Hence t>=gamma(S)-1. TRUE cannot occur in this OR region
of a proper output; FALSE, copies and shared operands do not break the count.

If the intersection of two factor supports has a common neighbor, their
no-common-neighbor regions are disjoint. The same condition puts one such
region outside the entire ancestor cone of the other output. For fixed i,
let z_i be the number of other no-common-neighbor factors. Choose J among
them with common-neighbor intersections both against S_i and pairwise
within J. The outside-cone count improves to

    B_i = z_i + max_J sum_(j in J)(gamma(S_j)-2).

Combining with the earlier distinct owner charge d_i gives

    m >= L(S_i) + d_i + B_i.

The sum only counts disjoint regions; arbitrary region overlap does not
justify adding bonuses. The formula also holds when the distinguished
residual graph is empty: |S_i|-1 OR support nodes plus the distinct charged
ANDs directly bound the cone, and the outside-cone counts remain disjoint.
Thus the previous joint-cost theorem's empty-residual restriction can be
removed by this separate counting argument. In terms of the number r of
no-common-neighbor factors, the bound is

    r <= m-L_i-d_i+indicator(C(S_i)=empty)
         - max_J sum_(j in J)(gamma(S_j)-2).

It is a family-dependent bound, not a uniform cap on r. Different supports
with the same MIS rejection pattern need not have the same gamma, owners
or intersection compatibility, so pattern compression alone cannot carry
these stronger predicates.

Two independent gamma methods agree on all2048 supports. Of909 eligible
no-common-neighbor supports,568 have gamma2 and341 gamma3. Of24 relevant
pure-OR vertex-cover supports,22 have gamma3 despite their low individual
costs. Each of those24 factors rejects exactly one MIS: its independent
complement must equal a maximal independent input to be nonredundant.

The concrete minimal support family [1280,85,1160,584,1778] demonstrates
strict improvement. Factor1160 has L=14 and two distinct other owners7,10
in its support. Pure-OR factor1778 has L=6 but gamma3, requiring at least two
no-common-neighbor OR gates outside that cone. The lower bound rises from
14+2+1=17 to14+2+2=18. The families [1280,85,1722,584,1778] and
[1408,592,176,1870,1898] likewise pass the old joint bound but need18 under
the new count. These exclude specific support families, not their entire
(k,r) classes or all alternative supports with the same row patterns.

Source `check_no_common_regions.py`, SHA
`3d62462bc32aadc614edffc3caa70b2cb504d6ea8468df853fb1a1e04bead8a8`,
and validation SHA
`3ce60572b6c763507f926f85105f4e4d943f736228af0c7b16b0b3f8a9bd9a9d`
retain all gamma witnesses,67 explicit obstructions to covering1778 with
at most two neighborhoods, and33 actual shared/copy/constant DAG controls.
Each control verifies its full product on all2048 inputs and the actual
region, boundary, disjointness and outside-cone counts. The scalar check
exits0 in0.039s with empty stderr. No solver or production change occurred.

## No-common-neighbor and mixed-triple census: independent PASS

Both S01 handoffs pass source binding, mathematical completeness review,
and independent finite verification: `no-common-cover-handoff.json`, SHA
`a4f80666a2c3de18353fbc10a24ec0bcf6a035a7b027f31854086baf15aa4a76`,
and `mixed-triple-handoff.json`, SHA
`159ca97f5b0d24fec9f727e8a58d93648f23cec92b6ef6e323ab7f754b570b8d`.

Since every no-common-neighbor selected output lies outside every other
selected cone, a17-gate prefix requires L_i<=18-r for such a factor and
L_i<=17-r for a factor having a common neighbor. This includes empty
residuals without the stronger owner charge. Distinct output positions
impose the usual sorted last-k capacities. The958 exact eligible supports
compress to382 rejection-pattern/status groups (339 no-common-neighbor,
43 with a common neighbor). Taking minimum cost within a group is safe for
this necessary relaxation, since no owner/ancestry predicates are transferred.
Equal rejection patterns cannot occur in a minimal family.

The independent checker rebuilds all2047 proper-support costs by both
maximum independent sets and edge-branch recursion, checks all958 source
records and382 groups, and verifies the eleven reported feasible (k,r)
representative witnesses. It independently finds zero no-common-neighbor
pattern triples at cost cap15 (328 patterns), one at16 (334 patterns), and
four at17 (339 patterns). Therefore k3/r3 is excluded under the precise
17-gate productive clean, proper full-cover, minimal-family hypotheses.
The eleven other probe results are explicit relaxation witnesses only.

For the complete mixed census, the reviewer enumerates rejection-pattern
triples first and then expands actual support representatives with their
exact costs. This differs from the producer's958-support pair enumeration.
No eligible pair of patterns covers all24 MIS, so every covering triple
has three distinct patterns and is minimal. The4217 exact covered-triple
expansions reproduce every count and every stored support family:

|r|exact-r covers|slot pass|joint pass|position pass|
|--|--:|--:|--:|--:|
|1|2046|2008|923|800|
|2|114|114|68|68|
|3|0|0|0|0|

The independent position checker enumerates chronological transitive
relations and reverses the position traversal. All16208 tested choices,
all saved witnesses and all accept/reject decisions match. The no-common-
neighbor ancestry prohibition, intervening-AND counts, outside-chain
subtraction and nonempty-residual owner charges are sound necessary tests.
Optional stronger cone-union/raw-input inequalities are omitted here.

All936 no-common-neighbor occurrences in the868 surviving families have
gamma2. Three r1 survivors have an edgeless-residual factor; no r2 survivor
does. The separately marked gamma/empty-residual column removes none and
is unnecessary for the accepted800/68/0 counts. Every surviving position
pattern remains an abstract necessary-condition witness, not a circuit.

Own `review_mixed_triples.py`, SHA
`64515af1a216ca0aec1a9b15993c19e0b2bcd7e13eea660bca0cd81e803e0b55`,
produces `mixed-triple-review.json`, SHA
`53fc2b6320a335c37abe9472894fff9a8ebea3ab812b6ede8dce9dc81eac016a`,
with full per-family results and independent witnesses. It exits0 in1.258s
with empty stderr. S01's pre-census NameError source/logs are preserved;
the corrected completed run alone supplies the reviewed result. There is
no whole AAAA/shard, Lean or arbitrary21-gate lower-bound conclusion.

## Pure four/five-factor cost-cover obstruction

The proposed pure-case caps L_i<=14 for k=r=4 and L_i<=13 for k=r=5 do
not exclude these classes. A separate bounded scalar search finds explicit
minimal full-cover function families with gamma2 throughout:

|k=r|support masks|individual costs|joint/region costs|
|--|--|--|--|
|4|1408,592,1546,501|11,12,10,6|14,15,13,9|
|5|1408,592,1866,501,1722|11,12,7,6,6|15,16,11,10,10|

All factors lack a common neighbor. Private MIS witnesses establish exact
minimality; all4096 input rows across the two families verify product F.
The selected-output antichain and distinct-slot relaxations also pass.
Because every gamma is2, the new outside-region bonus vanishes. These are
precise obstructions to closing either class using only the proposed cost,
MIS-cover, slot and current region conditions. They are not shared17-gate
prefix constructions and do not show that either pure case is realizable.

Source `no-common-neighbor/check_pure_four_five.py`, SHA
`6400a3b0c69bbcf525c893dfb973184d3c223f9101a95c3e6e208b48fd47d038`,
result `pure-four-five-validation.json`, SHA
`9bb0dc01ef29cae8ca9f70ff226ce8a7633fcab607cc7432cd4629b2f627bc3b`,
and full logs retain both families and every truth row. The search uses129
DFS nodes and0.0175 CPU seconds, well below the requested30-second limit.
S01 retains the separate68-r2 tight-layout analysis; it was not duplicated.


# S04 independent forest / two-sink / partial-twins review

Verdict: mathematical and finite PASS for the exact producer versions pinned
by forest-sinks-review.json (b57049af7a3c7e56f8bf964357e9ef5451876dd98483589be529be22599dad8c).
This is research evidence about minimal proper full-cover selected factors of
a 17-gate productive clean prefix for the fixed 11-vertex graph. It is not a
Lean proof, generated CNF cut, SAT certificate, or arbitrary circuit lower bound.

The independent script review_forest_sinks.py has SHA256
147af92a65bc8d07a1c370aa429be0c4cc1082219647008dd00d4f300a93d30e.
It checks all producer bindings, computes residual covers by edge branching,
enumerates the possible level partitions independently, and checks every
stored support family, operand split, shared-core obstruction and witness.
Its full stdout/stderr are preserved. It completed in 0.081 seconds with no
solver or Lean invocation. The four counted forest assignments are the ones
remaining after valid level/root/owner filters; this is not a claim that only
four total level assignments exist.

## Two-spare forests

With k selected outputs, c=15-k core gates and two additional nonselected
gates, min L>=c+1 and max L>=c+5 force a high-cost output to have two selected
ancestors. Distinct common-neighbor owners rule out merging these ancestors
at a single clean productive AND: on the same side their possible opposite
supports have empty intersection, and opposite sides would be dirty.
Two independent AND branches require another OR to form the proper final
support. Also an empty-support AND cannot directly feed another productive
AND. Thus the two spare ANDs form the chain A -> q1 -> B -> q2 -> C, with
selected outputs at levels zero, one and two. The corresponding cone limits
are c+1, c+3 and c+5. Level-zero outputs are tight and contain all c core gates.
The other operand forming a nonroot proper support is a core gate, not a raw
input or a different selected output. Its owner cannot belong to any root
support without forcing an extra gate in that tight root cone. All charged
gates are counted in the exact ancestor cones; no gate-minimality assumption
or global ancestry antichain has been inserted.

The independent finite enumeration reproduces four new exclusions among262
k3/r0 families and three among115 k4/r0 families, leaving258 and112. It also
excludes the last position-filter k5/r0 family, already covered by the earlier
k5/r0 closure. This does not address any r>0 class by itself.

## Two-sink tight cones

Let A,B have no common neighbors and let C have a common neighbor. Every
descendant of A or B is OR-only, so selected support incomparability makes
them terminal among the three. C -> A requires at least three gates outside
the C cone: the first AND must erase support, and an AND plus a single final
OR cannot create a no-common-neighbor support from a raw or C-cone operand.
Thus L_C>=14 forces an ancestry antichain in17 gates.

Each selected cone then has at most15 gates. An L=15 cone contains every one
of the14 nonselected gates. For every such tight support S, any core operand
support U of size at least2 must satisfy U subset S or CN(U) not subset S;
otherwise the supported-ancestor extra-gate charge contradicts tightness.
Raw singletons remain explicit exceptions. These Allowed tables are downward
closed. Each selected OR support must split into two allowed operand supports.
The chronologically last shared core gate directly feeds each tight output,
so its support lies in their intersection; the complementary operand test
then gives the shared-core obstruction. All statements apply symmetrically
to tight outputs, not just to C.

The finite checks independently reproduce23 v1 exclusions and42 symmetric
v2 exclusions across all68 mixed-r2 families. All21 distinct Allowed tables,
1979 immediate downward-closure checks, and all operand decompositions and
shared-core tests match the producers.

## Eight absorption cases

These have A support{6,8}, L_A=15; C support{4,5,9} or N(8), L_C=13 or12;
and B one of{3,7,8},{3,8,10},{7,8,10},{3,7,8,10}. The unique owner8 belongs
to A and B. Joint cost is17. If C is not an ancestor of A, any C->B path
removes C, B and its first AND from A's cone, contradicting L_A=15. The
remaining antichain case makes all C operands lie in A's tight core, where
each nonsingleton subset of C's support triggers the owner charge; two raw
singletons cannot cover C's support.

If C is ancestral to A, the A cone has16 gates and C has12 or13. The first
AND q below C has other support{8}. For a13-gate C cone the only AND outside
it is q. Replacing q=C AND R by R preserves all positive values because C
covers every edge; on independent inputs R=x8, already accepted by A and B,
and all descendants are OR. It deletes one gate and contradicts joint17.

For a12-gate C cone, C=N(8). A gate R inside C's cone would give actual raw8
ancestry and contradict the irrelevant-input charge. If R is raw8, then
q<=x8 and A,B have unaffected OR-only raw8 paths, so q->FALSE preserves their
full functions. Since q is clean, it was already FALSE on every independent
input. Consequently EVERY retained wire value on those inputs, and hence all
singleton supports, remains unchanged: retained ANDs stay clean and productive
without any restoration. If R is a gate outside C, the fourth outside gate
must be OR, returning to the q-only-AND argument. No uncounted overlap or
constant/copy exception is used.

These eight cases are disjoint from the42 symmetric cases. Sixteen actual
DAG controls cover q->FALSE and q->R, including AND descendants in the FALSE
case, and materialize the one-gate deletion. They verify98304 selected-output
equalities and49000 negative-wire equalities. The controls are not17-gate
search results and do not replace the budget proof.

## Partial twins

Family[276,518,1056] has L=[14,14,15], C=N(2), and raw2 cannot be ancestral
to tight C. Thus A=2 OR P and B=2 OR Q with core supports P={4,8}, Q={1,9}.
Both accept all required edges not incident to2. Each residual graph has
eight edges and cover number4, witnessed independently by triangle{3,6,7}
plus two disjoint edges and a size-four cover. The partial-edge cone bound
is13. P and Q cannot be ancestral to one another without requiring at least
15 core gates. Their13-gate cones therefore share all12 remaining core gates.
The last shared core signal has empty support, forcing P's other operand to
have support{4,8}. This operand is ancestral to Q, and CN({4,8})={1} lies in
Q's support, while {4,8} is not contained there. The partial supported-ancestor
charge forces Q>=14, a contradiction. This excludes one additional family.

Thus this frozen package leaves17 of68 k3/r2 families. Any later birth-count
closure is separate and is NOT included in this PASS. k3/r1 remains800 here;
pure k4/r4 and k5/r5 remain open with explicit relaxation witnesses.


# S04 forced-birth review: PASS with an explicit nonempty-H guard

The new argument closes the previously reviewed17 remaining k3/r2 support
families, conditional on the already reviewed17-gate productive-clean-prefix
normalization and complete mixed census. One family needs at least19 gates;
the other16 need at least18. With51 earlier exclusions, all68 surviving
mixed-r2 families are excluded. This is a mathematical and finite review,
not a Lean proof, implemented CNF restriction, SAT result or whole-shard claim.

The producer proof reviewed is forced-birth-terminal-bound.md, SHA256
ce4af7f97ca5ac57c10f10d85467daa6f9e9e33ec79a66f461769dfbc55c980a.
Its unrestricted strict statement has a genuine degenerate counterexample:
in the triangle on0,1,2, the three terminal OR gates(0,1),(0,2),(1,2) are
proper full-cover factors, have supports of size2, form an ancestry antichain,
and their product is the triangle edge function. H is empty, the core is
empty, and the terminal-star condition holds. The proposed bound says3>=4.
The failed step is choosing a last gate in the empty core.

Repair: require |E(H)|>0 for the strict bonus, or separately require a
nonempty retained core. Every application here has14 or16 edges in H, so the
repair does not change any exclusion. The independent finite source applies
the explicit nonempty-H guard. The original producer text and finite output
are retained unchanged as reviewed historical artifacts, with this correction.

## Exact helper interface and pruning

The existing edge_finset_gate_bound and edge_finset_gate_bound_partial were
read in the named Lean file without editing or compiling it. Their support
interfaces need only topologically earlier parents, singleton-or-empty raw
supports, empty AND support, OR support union, complete joins at ANDs, the
C4-free one-small-side property, and a birth cover for the graph being counted.
Neither helper requires a designated output or an exact function at a core
wire. A read-only snapshot and the original file hash are retained.

Pruning to the ancestor union of the k selected outputs makes those outputs
terminal because they are a syntactic ancestry antichain. Their nonempty
supports imply OR gates. Deleting them therefore retains every AND and all
its operand computations. Remove unused TRUE and reindex the remaining
inputs/gates in topological order before applying hsmall. TRUE cannot occur
on a retained path: its full support has no common neighbor in a loopless
graph, so productivity precludes a first AND descendant, while an OR-only
path would make a selected support full. FALSE and copies cause no problem.

For each edge of H, an output accepts that edge despite rejecting both
singleton endpoints. The edge-birth lemma yields a cross-support AND birth
in its core cone. Let B be the union of cross-support edges over every core
AND. Cleanliness gives B subset G, so B is C4-free. The counting helper gives

    |H| <= |B| <= #core AND + #core OR with support size>1
                     <= #core gates <= m-k.

Repeated births and shared ancestors are counted by the existing helper;
this argument does not sum individual output costs or count distinct ANDs
as distinct graph edges.

## Equality contradiction with H nonempty

Assume |H|=m-k. Then every inequality is equality, the core is nonempty, and
B=H. Pruning to the ancestor union of all core ANDs preserves all AND operand
computations and B. If it deletes any core gate, the same helper contradicts
|H|=m-k. Thus each core gate is ancestral to an AND (including itself).

Suppose a core gate has the exact support S_i of a selected output. Follow
it to a first AND q. The OR-only segment before q puts S_i in one operand.
Productivity supplies an element u of the other operand, and cleanliness
puts u in CN(S_i). If CN(S_i) is empty there is an immediate contradiction.
Otherwise every edge u-v for v in S_i is born at q. The terminal-star
condition says these edges are outside H, contradicting B=H.

The last core gate must itself be AND, since it is ancestral to one. It is
live after initial pruning and has no later core gate, so it directly feeds
a selected terminal OR. Its support is empty, forcing the other operand to
have exact support S_i. Since |S_i|>=2 and S_i is proper, that operand is a
gate rather than a raw input, FALSE or TRUE. It cannot be another selected
output by ancestry incomparability. Thus it is a forbidden core gate. This
proves m>=|H|+k+1 under the nonempty-H and terminal-star hypotheses. No
minimum-size or no-dead-gate assumption was inserted into the original prefix.

## Finite application and scope

All18 v2 survivors have one common-neighbor support of cost at least14.
The independently reviewed three-new-gates lemma therefore makes the three
selected outputs an ancestry antichain in17 gates. One family[384,592,1034]
has16 forced edges and the basic count already requires19 gates. The other17
have14 forced edges. Their common support has a unique owner belonging to
both no-common-neighbor supports, so every terminal star edge intersects all
three supports and lies outside H. The strict count requires18 gates.

One of those17 was already excluded by partial twins. The exact current
remaining set therefore splits into ONE basic and SIXTEEN strict exclusions.
The independent script verifies the exact17 binding, all18 edge sets and
owner conditions, individual costs by a separate brute-force cover calculation,
36864 complete truth rows, full-factor product and proper-subproduct witnesses,
and the exact disjoint union51+17=68. It also retains the triangle countermodel
and a sharp nonempty-H control: G consists of disjoint edges01 and23; the
single factor(0 OR1) OR(2 AND3) has m=3, k=1, |H|=1 and attains the repaired
strict bound. These controls verify concrete edge cases, not the general proof.

Independent source review_forced_birth.py SHA256
624c39cbebd076ec2e4925200d44396366c42ae2a275264f39a567f5261a41a9;
result forced-birth-review.json SHA256
8ccc9ad77b0a23d8c91c7141cf7627e26b2f0d64589a994cd35a21f1f26fa500.
The run exited0 in0.057 seconds with empty stderr. The named Lean file remains
SHA256 0e0620c89307cf34be010940037cb187797eea76c85fc8c8a89b9bd1cfc56e5c.

The surviving common-neighbor counts remain258 k3/r0 and112 k4/r0; k3/r1
remains800 at this checkpoint. Pure k4/r4 and k5/r5 remain open. This review
does not convert support-family exclusions into unreviewed CNF clauses or
claim that the full21-gate proof gap has been closed.


## Final scope checks and routing-correction preservation

The new guarded simultaneous birth inequality alone also leaves the two
previous pure-case relaxation witnesses alive: k4 family[1408,592,1546,501]
has12 forced edges and lower bound17; k5 family[1408,592,1866,501,1722] has10
forced edges and lower bound16. This is a direct check of two existing
families, not a repeated cover search. A useful next condition must charge
additional terminal-support assembly or characterize equality; repeating
the previous cost/MIS relaxation cannot close these classes.

The misrouted134227 work was only full scalar evaluation, pruning and merging
repeated expressions. No S04 repair search was run. Best1 is F OR x9 with22
full false positives,20 live gates reduced to19 by merging duplicate8 OR9.
Best3 is F with edge(2,5) deleted,24 full false negatives,0 false positives,
and20 clean live gates. Full sources,4096 truth rows, copies and logs are in
candidate134227-analysis-preservation-v1.tar.gz, SHA256
85f85f4274357bb2f316b3074c65a2c98f797c49448becef7730207ae18e6d46,
20264bytes/15regular members. S05 owns all later candidate work.

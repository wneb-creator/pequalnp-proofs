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

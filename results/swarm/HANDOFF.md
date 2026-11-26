# L-meta-2590 research handoff

This branch contains partial research, not a submission or a proof of the posted gap. No FINAL or pull request has been issued. The desk lease belongs to the coordinator and must not be released here.

## Independently checked cases

`RemainingThree.lean` is the strongest assembled research result: any hypothetical size-at-most-19 monotone circuit computing the posted Petersen function yields a correct strict-live circuit of the same allowed size, with vertex 0 ineligible, Bzero=0, Bplus=eligible-cardinality+1, and saturated support exactly `{1,4}`, `{1,4,5}`, or `{3,6,7}`. Its full imported kernel check, final theorem type, standard-three-axiom audit, and independent source review passed. There are no added case assumptions; the three exclusions themselves remain open in this composition.

`RemainingOne.lean` is the checked intermediate result: every hypothetical monotone circuit of size at most 19 computing the posted Petersen function normalizes to a correct strict-live DAG of length at most 19 with exactly one ineligible vertex. Its imported kernel build and exact-type/standard-three-axiom audit passed. It is a research composition, not a permitted single-file submission.


- `FoundationI0I3I4.lean` normalizes the exact posted circuit semantics and excludes ineligible cardinalities 0 and 4 and the extendable cardinality-3 orbit. Its remaining alternatives are cardinalities 1, 2, and the canonical neighborhood `{1,4,5}`. Its full kernel build and six axiom audits passed. At 681941 bytes, it exceeds the final 512 KiB cap.
- `CenterThreeExits.lean` is the exact helper-2 source from `f563fe03ac673e0f26e6dd839b3859e3d7df97f5` (259650 bytes; SHA256 `0bb93e99565a646b2624e5ec56a3ff8e9bd9eb51099f3c1f36bc0ce6e7ae22b2`). Its closed endpoint assumes only a strict live correct Petersen circuit, the neighborhood contained in the ineligible set, at most three exits at vertex 0, and length at most 19. Root independently rebuilt it and checked its type, axioms, and source. There is no abstract C6 lower-bound premise.
- `NeighborhoodCase.lean` closes the entire canonical neighborhood case: only strict liveness, correct Petersen computation, exact ineligible set `{1,4,5}`, and length at most 19 are assumed. Full combined kernel build and six standard-three-axiom audits passed, as did independent source, graph-bridge, and exact relocation reviews. The file is 355859 bytes, SHA256 `78c4c4242296ea4f5ec3efd0607950b5c729378b97f889520f902701f9596b64`. It splits on Bzero and discharges all virtual-extension, birth, and C6 obligations internally.
- `OneIneligibleCensus.lean` is exact h3 `f06c5b441bb366d79fd53a6385718d7ff5cb43ea`, 474126 bytes. Root independently checked the actual support dichotomy, full-A six-gate witness, and complete r1 reduction, including types and standard axioms. Under strict liveness, correct Petersen computation, vertex 0 ineligible, Bzero=0, and Bplus=eligible-cardinality+1, it preserves the circuit length and hypotheses while reducing to saturated support `{1,4}`, `{1,4,5}`, or `{3,6,7}`. Those three exclusions remain obligations.
- `R0Resource.lean` is the exact 146805-byte h8 `da7ff2555a54921a2091007dd6a4c93c2c208ac7` resource proof, freshly rebuilt by root. `R0CurrentAdapter.lean` restores the omitted old h3 declarations, proves the required empty-input-support facts, and closes the r0 branch. Its final actual canonical-I1 reduction and standard-axiom audits passed. `RemainingThree.lean` also connects arbitrary-one-ineligible canonicalization using checked Petersen automorphisms.
- `ExclusiveFamilies.lean` constructs actual disjoint nonempty exit families when Bzero is zero. Selected exit outputs have empty singleton support; source intersections are the three required neighborhood triples. It does not itself append virtual gates or exclude the whole neighborhood case.
- `C6DesignatedBound.lean` gives the actual strict C6 bound with distinct designated gate wires and joint opposite-pair membership. The older `PairPruning.lean` still has an explicit live-bound hypothesis.

## Selected external publications

Helper branches are on the fork under `pnp/swarm-L-meta-2590-h1` through `-h9`. The following are peer publications; the root checks described above must not be inferred for other snapshots.

- h1 `aaca3ef59820d2cd959624599d9eb39113e516b4`: complete cardinality-2 exclusion, 454286 bytes. Root independently checked this exact source by full kernel build, endpoint type/standard-axiom audit, source review, and replay of all 134 certificate trees; it is archived as `TwoIneligible.lean`. The peer compact update `b218474a1fe16b5a6ea16a6cc2a43bb7c79aad39` is 389076 bytes and has not been independently rebuilt by root.
- h2 `56c012f4b5a031c3ef00b37d34fc0382b1b23294`: 236482 bytes, combines the closed three-exit, selected-empty-exit/virtual-mark, and actual virtual-triple endpoints after literal core deduplication. Root exact transformation review passed; the complete neighborhood assembly passed its kernel build.
- h5 `ea83c08f77253d819e9ec157f69ef97313e5fe9a`: complete cardinality-3 case, 376910 bytes, including a smaller full-neighborhood proof. Earlier virtual construction is retained in `fda4c8cfdc19047759abeafca2793140ac9d4f12` and bus 4862/4872. Source wire IDs must be deduplicated; its cost inequality correctly accounts for this.
- h7 `d1daedf4911a826470fc33649823562daa5a4337`: positive-Bzero canonical-neighborhood case reduces to at most three center exits.
- h3 `f06c5b441bb366d79fd53a6385718d7ff5cb43ea`: actual three-case census and full-A source witnesses, now independently rebuilt and archived by root. Three canonical exclusions remain in progress.
- h6 `a1da66a9621c13e4c6b5dbc80ea1341c2f4d6770`: complete cardinality-4 exclusion plus both actual normalized S50 source classifications, including the omitted paired-leaf layouts. This is not a full S50 resource exclusion.
- h8 `37dce1c17aac0e1e6c452339ed44da0cfa18b46d`: actual resource exclusion for one S18 profile; full S18 profile exhaustiveness remains separate. Further S200 and S50 resource work is ongoing.
- h9 `11daf304237854f82708c45904d42c3897790e82`: zero-ineligible proof, general six births, and designated-wire pruning. This publication includes the guard-only identifier corrections.

## Remaining blockers and cautions

The checked actual-circuit composition now leaves exactly the three canonical saturated supports S18/S50/S200. The r0 restoration, arbitrary-one-ineligible-to-vertex-0 relabeling, and complete actual support census are connected and kernel-checked. None of the three exclusions is assumed proved by `RemainingThree.lean`. The advertised twelve S50 profiles are not exhaustive under the stated static constraints: helper 6 supplied an additional static profile, and root independently replayed its 15-edge coverage, seven disjoint operand pairs, exact exit counts, and all 400 nonvacuous exposure constraints over 76 independent masks. This is not a circuit counterexample.

The final combined source has not been made to fit 512 KiB. Safe identifier/whitespace experiments on the checked foundation reach 603719 bytes but have only parser checks, not a full kernel build. No compressed candidate is a validated submission.

Temporary AND extensions preserve the original prefix and are strict; they need not be live or compute the original output. Use the generic six-birth theorem on the extension. Empty singleton support does not mean a Boolean function is false. Distinct exit arcs need not have distinct source wires. Distinct designated gate wires are essential for the pruning count.

The actual outside guard rejects the substring `notation`, including identifiers containing `annotations`. Rename those helper identifiers to `marks`, and remove `_root_` qualifications before final submission. Helper-2 f563 already has these corrections. Run the actual guard and exact posted-theorem checker on any eventual final file.

## Reproducing the imported research result

In this prepared workspace, run:

```sh
bash results/swarm/reproduce_remaining_one.sh /tmp/oec/pnp-swarm-2590-orch/reproduce-all
```

The preparation script pins the three archived source hashes, restores plain modules under their audited import names, and applies the exact checked 143-prefix namespace relocation to the two-ineligible source. It then copies `RemainingOne.lean`. Preparation was executed and all generated proof sources matched the checked sources byte for byte; Python/Bash syntax checks passed. The wrapper and its modules have already passed their recorded kernel builds; the complete reproduction script has not been rerun as an additional full build. Complete future build diagnostics go to the selected scratch directory.

For the stronger checked three-profile composition, run:

```sh
bash results/swarm/reproduce_remaining_three.sh /tmp/oec/pnp-swarm-2590-orch/reproduce-three
```

This prepares and builds eight modules, including the exact seven-prefix h3 relocation and restored r0 bridge. Source preparation was executed independently and all eight materialized proof sources matched the checked sources exactly; Python/Bash syntax checks passed. The full script has not been rerun as a duplicate complete build.

Late research caution: helper 3 reports that the remaining pure-frame analysis for support `{1,4}` (mask 18, called S14 in helper messages) includes a branch where one designated AND gate has singleton support `{5}`. Its complete resource exclusion is still open. Do not extend S50's all-AND-empty-support assumptions to that branch. Helper finite resource certificates and Python model exhaustion do not by themselves prove actual-circuit simulation.

# L-meta-2590 research handoff

This branch contains partial research, not a submission or a proof of the posted gap. No FINAL or pull request has been issued. The desk lease belongs to the coordinator and must not be released here.

## Independently checked cases

`RemainingOne.lean` is the strongest assembled research result: every hypothetical monotone circuit of size at most 19 computing the posted Petersen function normalizes to a correct strict-live DAG of length at most 19 with exactly one ineligible vertex. Its imported kernel build and exact-type/standard-three-axiom audit passed. It is a research composition, not a permitted single-file submission.


- `FoundationI0I3I4.lean` normalizes the exact posted circuit semantics and excludes ineligible cardinalities 0 and 4 and the extendable cardinality-3 orbit. Its remaining alternatives are cardinalities 1, 2, and the canonical neighborhood `{1,4,5}`. Its full kernel build and six axiom audits passed. At 681941 bytes, it exceeds the final 512 KiB cap.
- `CenterThreeExits.lean` is the exact helper-2 source from `f563fe03ac673e0f26e6dd839b3859e3d7df97f5` (259650 bytes; SHA256 `0bb93e99565a646b2624e5ec56a3ff8e9bd9eb51099f3c1f36bc0ce6e7ae22b2`). Its closed endpoint assumes only a strict live correct Petersen circuit, the neighborhood contained in the ineligible set, at most three exits at vertex 0, and length at most 19. Root independently rebuilt it and checked its type, axioms, and source. There is no abstract C6 lower-bound premise.
- `NeighborhoodCase.lean` closes the entire canonical neighborhood case: only strict liveness, correct Petersen computation, exact ineligible set `{1,4,5}`, and length at most 19 are assumed. Full combined kernel build and six standard-three-axiom audits passed, as did independent source, graph-bridge, and exact relocation reviews. The file is 355859 bytes, SHA256 `78c4c4242296ea4f5ec3efd0607950b5c729378b97f889520f902701f9596b64`. It splits on Bzero and discharges all virtual-extension, birth, and C6 obligations internally.
- `OneIneligibleCensus.lean` is exact h3 `f06c5b441bb366d79fd53a6385718d7ff5cb43ea`, 474126 bytes. Root independently checked the actual support dichotomy, full-A six-gate witness, and complete r1 reduction, including types and standard axioms. Under strict liveness, correct Petersen computation, vertex 0 ineligible, Bzero=0, and Bplus=eligible-cardinality+1, it preserves the circuit length and hypotheses while reducing to saturated support `{1,4}`, `{1,4,5}`, or `{3,6,7}`. Those three exclusions remain obligations.
- `ExclusiveFamilies.lean` constructs actual disjoint nonempty exit families when Bzero is zero. Selected exit outputs have empty singleton support; source intersections are the three required neighborhood triples. It does not itself append virtual gates or exclude the whole neighborhood case.
- `C6DesignatedBound.lean` gives the actual strict C6 bound with distinct designated gate wires and joint opposite-pair membership. The older `PairPruning.lean` still has an explicit live-bound hypothesis.

## Selected external publications

Helper branches are on the fork under `pnp/swarm-L-meta-2590-h1` through `-h9`. The following are peer publications; the root checks described above must not be inferred for other snapshots.

- h1 `aaca3ef59820d2cd959624599d9eb39113e516b4`: complete cardinality-2 exclusion, 454286 bytes. Root independent full kernel build, exact endpoint type, standard-three-axiom audit, source review, and replay of all 134 certificate trees passed. The exact source is archived as `TwoIneligible.lean`.
- h2 `56c012f4b5a031c3ef00b37d34fc0382b1b23294`: 236482 bytes, combines the closed three-exit, selected-empty-exit/virtual-mark, and actual virtual-triple endpoints after literal core deduplication. Root exact transformation review passed; the complete neighborhood assembly passed its kernel build.
- h5 `fda4c8cfdc19047759abeafca2793140ac9d4f12`: 385653 bytes; additional neighborhood structure and the checked virtual-AND construction from bus 4862 and 4872. Source wire IDs must be deduplicated; its cost inequality correctly accounts for this.
- h7 `d1daedf4911a826470fc33649823562daa5a4337`: positive-Bzero canonical-neighborhood case reduces to at most three center exits.
- h3 `f06c5b441bb366d79fd53a6385718d7ff5cb43ea`: actual three-case census and full-A source witnesses, now independently rebuilt and archived by root. Three canonical exclusions remain in progress.
- h6 `1792b0f5d072a00e464f9d959f9d69c9261002e3`: complete cardinality-4 exclusion plus one-ineligible structural lemmas.
- h8 `e0113b8811e8aba0b5b77263815883baf1fb9024`: checked finite resource certificate for one S18 profile; actual profile exhaustiveness remains separate.
- h9 `11daf304237854f82708c45904d42c3897790e82`: zero-ineligible proof, general six births, and designated-wire pruning. This publication includes the guard-only identifier corrections.

## Remaining blockers and cautions

The checked actual-circuit composition now leaves only the one-ineligible case. Within r1, the actual support census is checked; S18/S50/S200 exclusions remain unfinished. The r0 branch needs restoration and composition of checked declarations pruned from the latest h3 export (old commit `9edbe3499f94213015600ba33428725e42e559d8`, bus 3577/4055), and arbitrary-one-ineligible-to-vertex-0 relabeling still needs its final connection. These are separate from the three r1 branch obligations. The advertised twelve S50 profiles are not exhaustive under the stated static constraints: helper 6 supplied an additional static profile, and root independently replayed its 15-edge coverage, seven disjoint operand pairs, exact exit counts, and all 400 nonvacuous exposure constraints over 76 independent masks. This is not a circuit counterexample.

The final combined source has not been made to fit 512 KiB. Safe identifier/whitespace experiments on the checked foundation reach 603719 bytes but have only parser checks, not a full kernel build. No compressed candidate is a validated submission.

Temporary AND extensions preserve the original prefix and are strict; they need not be live or compute the original output. Use the generic six-birth theorem on the extension. Empty singleton support does not mean a Boolean function is false. Distinct exit arcs need not have distinct source wires. Distinct designated gate wires are essential for the pruning count.

The actual outside guard rejects the substring `notation`, including identifiers containing `annotations`. Rename those helper identifiers to `marks`, and remove `_root_` qualifications before final submission. Helper-2 f563 already has these corrections. Run the actual guard and exact posted-theorem checker on any eventual final file.

## Reproducing the imported research result

In this prepared workspace, run:

```sh
bash results/swarm/reproduce_remaining_one.sh /tmp/oec/pnp-swarm-2590-orch/reproduce-all
```

The preparation script pins the three archived source hashes, restores plain modules under their audited import names, and applies the exact checked 143-prefix namespace relocation to the two-ineligible source. It then copies `RemainingOne.lean`. Preparation was executed and all generated proof sources matched the checked sources byte for byte; Python/Bash syntax checks passed. The wrapper and its modules have already passed their recorded kernel builds; the complete reproduction script has not been rerun as an additional full build. Complete future build diagnostics go to the selected scratch directory.

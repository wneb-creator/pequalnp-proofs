# L-meta-2590 research handoff

This branch contains partial research, not a submission or a proof of the posted gap. No FINAL or pull request has been issued. The desk lease belongs to the coordinator and must not be released here.

## Independently checked cases

- `FoundationI0I3I4.lean` normalizes the exact posted circuit semantics and excludes ineligible cardinalities 0 and 4 and the extendable cardinality-3 orbit. Its remaining alternatives are cardinalities 1, 2, and the canonical neighborhood `{1,4,5}`. Its full kernel build and six axiom audits passed. At 681941 bytes, it exceeds the final 512 KiB cap.
- `CenterThreeExits.lean` is the exact helper-2 source from `f563fe03ac673e0f26e6dd839b3859e3d7df97f5` (259650 bytes; SHA256 `0bb93e99565a646b2624e5ec56a3ff8e9bd9eb51099f3c1f36bc0ce6e7ae22b2`). Its closed endpoint assumes only a strict live correct Petersen circuit, the neighborhood contained in the ineligible set, at most three exits at vertex 0, and length at most 19. Root independently rebuilt it and checked its type, axioms, and source. There is no abstract C6 lower-bound premise.
- `NeighborhoodCase.lean` closes the entire canonical neighborhood case: only strict liveness, correct Petersen computation, exact ineligible set `{1,4,5}`, and length at most 19 are assumed. Full combined kernel build and six standard-three-axiom audits passed, as did independent source, graph-bridge, and exact relocation reviews. The file is 355859 bytes, SHA256 `78c4c4242296ea4f5ec3efd0607950b5c729378b97f889520f902701f9596b64`. It splits on Bzero and discharges all virtual-extension, birth, and C6 obligations internally.
- `ExclusiveFamilies.lean` constructs actual disjoint nonempty exit families when Bzero is zero. Selected exit outputs have empty singleton support; source intersections are the three required neighborhood triples. It does not itself append virtual gates or exclude the whole neighborhood case.
- `C6DesignatedBound.lean` gives the actual strict C6 bound with distinct designated gate wires and joint opposite-pair membership. The older `PairPruning.lean` still has an explicit live-bound hypothesis.

## Selected external publications

Helper branches are on the fork under `pnp/swarm-L-meta-2590-h1` through `-h9`. The following are peer publications; the root checks described above must not be inferred for other snapshots.

- h1 `aaca3ef59820d2cd959624599d9eb39113e516b4`: complete cardinality-2 exclusion, 454286 bytes. Root independent full kernel build, exact endpoint type, standard-three-axiom audit, source review, and replay of all 134 certificate trees passed. The exact source is archived as `TwoIneligible.lean`.
- h2 `56c012f4b5a031c3ef00b37d34fc0382b1b23294`: 236482 bytes, combines the closed three-exit, selected-empty-exit/virtual-mark, and actual virtual-triple endpoints after literal core deduplication. Root exact transformation review passed; the complete neighborhood assembly passed its kernel build.
- h5 `fda4c8cfdc19047759abeafca2793140ac9d4f12`: 385653 bytes; additional neighborhood structure and the checked virtual-AND construction from bus 4862 and 4872. Source wire IDs must be deduplicated; its cost inequality correctly accounts for this.
- h7 `d1daedf4911a826470fc33649823562daa5a4337`: positive-Bzero canonical-neighborhood case reduces to at most three center exits.
- h3 `96b1dfa5d02a519c7578c6a2d93a6e2bf8d369aa`: includes the closed S36 case and earlier one-ineligible subcases. The actual support dichotomy and orbit census are reported checked but are not yet in the root assembly; three canonical branches remain in progress.
- h6 `1792b0f5d072a00e464f9d959f9d69c9261002e3`: complete cardinality-4 exclusion plus one-ineligible structural lemmas.
- h8 `e0113b8811e8aba0b5b77263815883baf1fb9024`: checked finite resource certificate for one S18 profile; actual profile exhaustiveness remains separate.
- h9 `11daf304237854f82708c45904d42c3897790e82`: zero-ineligible proof, general six births, and designated-wire pruning. This publication includes the guard-only identifier corrections.

## Remaining blockers and cautions

The independently checked case results now leave only the one-ineligible mathematical case; their single actual-circuit composition is still being compiled. That case still requires integration of the actual support census and closure of the remaining S18/S50/S200 cases. The advertised twelve S50 profiles are not exhaustive under the stated static constraints: helper 6 supplied an additional static profile, and root independently replayed its 15-edge coverage, seven disjoint operand pairs, exact exit counts, and all 400 nonvacuous exposure constraints over 76 independent masks. This is not a circuit counterexample.

The final combined source has not been made to fit 512 KiB. Safe identifier/whitespace experiments on the checked foundation reach 603719 bytes but have only parser checks, not a full kernel build. No compressed candidate is a validated submission.

Temporary AND extensions preserve the original prefix and are strict; they need not be live or compute the original output. Use the generic six-birth theorem on the extension. Empty singleton support does not mean a Boolean function is false. Distinct exit arcs need not have distinct source wires. Distinct designated gate wires are essential for the pruning count.

The actual outside guard rejects the substring `notation`, including identifiers containing `annotations`. Rename those helper identifiers to `marks`, and remove `_root_` qualifications before final submission. Helper-2 f563 already has these corrections. Run the actual guard and exact posted-theorem checker on any eventual final file.

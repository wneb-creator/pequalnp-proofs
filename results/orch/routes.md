# Proof routes and sensitivity invariant

## Inspected reductions

- R_meta_1896_1 dualizes to an AND-count circuit with a true sentinel. Its third hypothesis is the unresolved 51 lower bound.
- R_meta_1896_347 supplies 36 cyclic masks (468 generic false rows) and leaves the same circuit lower bound as its other hypothesis.
- R_meta_4949_603 expresses this finite truth-table problem as a straight-line program containing only OR gates; each operand is an arbitrary conjunction of available wires. This is a potentially suitable finite search normal form, but does not itself prove a lower bound.

## Compiled partial results

Routes.lean generalized the first 514 lines of checked L_meta_5158, originally from willakone's L_meta_2059 counting argument. The hypothesis `tau p v = true -> v = p` is weakened to `c v = false -> tau p v = true -> v = p`. This lets the witnesses be single-coordinate changes above an arbitrary baseline. Compilation passed in routes-build-002.log. An OR cardinal inequality was then added; routes-build-004.log passes.

Normalize.lean prepends one false input, shifts existing wires by one, and sends all invalid/forward references to that sentinel. It preserves gate operations, gate count, and exact evaluation, while every reference becomes backward. Compilation of the foundational lemmas passed in normalize-build-002.log. The later combined Sensitivity.lean also contains exact OR-count and circuit-evaluation preservation.

Sensitivity.lean combines those components and derives `M.card - 1 <= number of OR gates` whenever a circuit is false at c and true at each tau p, with each tau p differing from c only at input p among coordinates false in c. This requires no ReadsBack assumption. Its generic build passed in sensitivity-build-003.log. The concrete consequence `Sensitivity.eighteen_from_tests` also passes in sensitivity-build-006.log and proves 18 OR gates from exactly the posted positive and negative tests (definitions only abbreviate them). Immutable snapshot: checked/routes-eighteen-or-gates.lean.

## Remaining mathematical obstacle

A single maximal false input gives 18 OR gates, below the target 51. Summing row-sensitive merge counts requires proving that an OR gate cannot serve too many rows. For generic-only negatives, standard normalization for exact quadratic edge functions does not apply automatically: the circuit may accept higher-degree independent sets corresponding to the omitted line/pencil rows.

Web search on allowed GitHub/pequalnp hosts (2026-11-25) found no usable primary-source theorem closing the gap; broad hits concerned unrelated arithmetic circuits. No unverified source claim is used in the proof.

## 2026-11-25T03:46:10.891322+00:00 — singleton-positive OR structure

Compiled DirtyOr.at_most_one_true: k false OR gates and at most k+1 total OR gates force any two true OR gates at the baseline to coincide. PairRows gives 25 generic seven-coordinate rows covering all same-side pairs, hence any three coordinates have two in one row. Under total OR count <=19, this proves at most two singleton-positive OR gates.

Compiled two_singletons_or_below by strong induction on wire index. A wire false on empty input but true on two distinct singleton inputs has an OR gate at or below that wire that is true on both. Thus, under uniqueness of the OR gate accepting each singleton, a nonconstant OR gate accepts at most two singleton coordinates. The union badCoords over all nonconstant singleton-positive OR gates consequently has cardinality at most four. This is intended for a >=20 consequence by deleting flags incident to those coordinates and applying CleanOrSkip.

Immutable snapshot: checked/routes-four-bad-coordinates.lean, SHA256 2aa1ebea94e88ecd2677734b4579ec79bd8a37c76089deb7c7a3bd6eb8480218, 1399 lines; adjacent full Lean log, exit 0. No ReadsBack premise in these final generic helpers.

Rejected full-proof shortcut: optional minimal terms are collinear/concurrent TRIPLES, not quartic lines/pencils, and such triples overlap in two coordinates. Even arbitrary graph minterms are linear while K2,2 has four edges and only two OR gates, so hypergraph linearity alone cannot yield the target bound. C4-freeness plus pure-side extra terms remains an unproved possible structural route.

## 2026-11-25T03:58:35.315140+00:00 — first-introduction partition

Compiled generic first-introduction structure, with no OR-count or ReadsBack assumption: freshCoords C j is the set of singleton coordinates first accepted by nonconstant OR gate j. Each set has cardinality at most two; sets are pairwise disjoint; their union is exactly badCoords. freshBlocks packages the nonempty sets. Monotonicity and disjoint false/true OR counts show every baseline with at least k false OR gates intersects at most q-k blocks when the circuit has at most q OR gates.

A first-introduction OR gate has a valid earlier operand that is false on every assignment avoiding its newly introduced coordinate. This follows from a backward AND trace: otherwise an earlier nonconstant OR gate would accept that singleton. Consequently such OR gates cannot merge surviving incidence flags and may be excluded from the clean survivor count.

Latest complete immutable snapshot: checked/routes-generic-row-capacity.lean, SHA256 ab8fa3b57d60d45a920d4d977f007931a9643cedaf68a82db5a01e62c1ea5d84, 1824 lines, matching full Lean log, exit0. It includes freshBlocks_capacity_sensitive_row for arbitrary seven-coordinate row certificates, suitable for PackingRows47. Previous snapshot hashes are in parent messages.

Independently reviewed checked/Twenty.lean SHA256 ec1f2f40f2cec0e24fb274911856e0a6dee7641f01b111e4dc171e954e657eed: semantic bridge and assembly valid; posted_twenty text equals exact posted statement with only51 replaced20; strict syntax scan passed. This is a partial20-OR lower bound, not the requested51.

## 2026-11-25T04:07:43.523710+00:00 — generic averaging bridge

Averaging.packing_union_card_le_eight compiled cleanly, snapshot checked/routes-averaging-eight.lean SHA256 abcbe71b43209bca6e4b35acf5f95fe4cbc917bc48fab8a4eef0958ae8ec58be (76 lines, empty successful log). It assumes 468 rows, disjoint nonempty blocks of size at most two, singleton touch counts >=126, distinct-pair union touch counts >=204, and row capacity <=2. Each block contributes at least78*card+48 touches. Double counting yields78*u+48*b<=936, whileu<=2*b; integer arithmetic forcesu<=8. No geometry computation is embedded in this generic proof.

Independent semantic review passed for checked/CleanOrExcludingGeneral.lean SHA256 434a371ff00a4f1308afc039832fcd17e35d05b2d5307d94517ea8285a031b05 and checked/WeightedSurvivors.lean SHA256 5e8cdf9ad17244249847e3181b411b8d9b660b3c851e3832a1f76e990543891f. The excluded gate index map preserves cardinality under normalization; backward dead operands map to a+1; the weighted composition only excludes first-introduction OR gates and uses freshBlocks.card<=excluded-gate-card. Format scans passed.

## 2026-11-25T04:10:06.098025+00:00 — symbolic rows and AllRows review

Symbolic maximal-row sensitivity compiled and frozen at checked/routes-symbolic-maximal-row.lean, SHA256 8c34db3ff26b33f41c7ce54d210505a8adb29d93dec8fdc8512a9084d7591b97,1931lines. The final107lines derive a sensitive incidence pair for every missing coordinate directly from maximality and rowInput semantics; no finite edgeFor table is required. or_lower_bound independently reviewed these107lines and reported pass to parent.

Independently reviewed AllRows.lean source SHA256 68bba49f71c30510ec294b3f0b563cd3b80c0d502656b857ac3ff5a771c4dac4 while its Lean build was pending. Literal tables parse as36x13 with468distinct rows. Recomputed posted maximality/noncollinearity/nonpencil conditions, rowInput equality, seven true coordinates,19 missing coordinates, singleton touches126, and distinct-pair union touches>=204. All finite statements are unconditional decide+kernel checks and their exact types supply Averaging/SymbolicRows. Syntax scan passed. Detailed JSON at checked/allrows-independent-review.json; this review does not itself claim the pending kernel build passed.

## 2026-11-25T04:30:32.251579+00:00 — capacity-three bridge preparation

Frozen concrete evaluator definitions are in scratch packing3-definitions.txt, wrapped in PEqualNP.Outside.L_meta_1896_aux. PackingThree.Block has vertices/active/edges masks. State has used/covered/seen/twice/thrice/count. Pruning checks flagCount(covered OR all candidate edges)<=29+currentcount.

Compiled concrete pruning semantics: checked/packing-mask-semantics.lean SHA256 9cb2858a54da1da2c2cc4a1963f2e6b3d98f526897cd5eb03163e6b0811f1e28 (136lines). or_lower_bound independently reviewed and passed. It proves monotonicity of flags and masks, selected-sublist coverage, count growth, and pruning soundness for arbitrary selected sublists.

Existing child quadratic_shadow compiled generic pruned DFS soundness, checked/packing-pruned-dfs-soundness.lean SHA256 d32326e551b11ed152612dc0f624a339487dbb7d8fa1114802a25df3a10dfe09,145lines; parent agent proof_routes independently reviewed it. Child also compiled checked/packing-three-trace-invariants.lean SHA256 03cbead3abd94b5135b90e6aecae964430cb4975a1d06db8a5582592aef20095,191lines; independent review JSON stored alongside. It proves row thresholds1/2/3 and valid traces from pairwise-disjoint vertex masks and row quotas, including fixed-prefix transport. Neither theorem asserts a concrete packing bound.

PackingFamilies.lean is drafted but not yet checked due kernel-slot coordination. Its generic Valid/removed definitions and encode_blocks proof map arbitrary disjoint nonempty coordinate blocks of size<=2 into an index family using completeness of vertexSet, preserving cardinality and coordinate union. Geometry owns finite masks/root/orbit certificates; or_lower_bound owns action-word normalization and22 assembly. Algebra exact31root search uses27two-pair roots with all compatible extensions,3one-pair roots with singleton-only extensions, and1singleton root with singleton-only extensions. Full family must be mapped under finite generator actions; no circuit permutation is required.

## 2026-11-25T04:31:38.072003+00:00 — resource-safe certificate chunking

Geometry stopped the monolithic31-root check at cgroup99.5%; it had not established the full bound. The successful811-node benchmark remains the only root certificate checked so far. Geometry is splitting each normalized root into indexed first-extension obligations, preserving the complete later candidate suffix. Frozen branchAt/chunk definitions are in scratch packing3-chunk-definitions.txt. Child quadratic_shadow is drafting generic branches reconstruction and chunk-member extraction in PackingChunkGlue.lean, with no Lean process until root grants a slot. Never split branches(A++B) into independent branches(A)&&branches(B): that would omit extensions of choices inA using candidates inB.

## Recovery and symbolic mask/assembly checks 2026-11-25T04:52:33.553133+00:00

Cached PackingRecordProofs survived the environment restart and independently passed semantic review. Frozen SHA 1f170c17c7ff54c81307e72bd1d01aac09ffbeeb4c368744766d40a89117427b.

PackingBoundedMaskProofs compiled exit 0: finite correctness and mask < 2^n imply exact full-Nat bit semantics. SHA 834803a7afe5a4dccc6061c5b9238114c8ccf0c3159c6cd22781af8c97a271dd, 32 lines, independent review passed by or_lower_bound.

PackingChunkAssemblyTest compiled exit 0: coverage of every indexed branch, matching root IDs, root good, and all chunk truths imply every rootCheck. The finite claims remain hypotheses. Authored by lean_setup, semantic review passed by proof_routes: each branchAt uses the complete original suffix; no branch combinations are lost. SHA 298b4b5342e86b9ea80ff73705c843ff5f6acd958ce674fc7c1ee7bd597856b7, 43 lines.

Both exact modules and complete logs are frozen under checked/modules. No concrete all-root packing bound is claimed. Large finite packing evaluation remains paused; small Lean slot released.

## Canonical compiler pivot

Parent paused expensive capacity-three packing: even capacity-four has a large obstruction, so this cannot reach the posted51. New task: generic compiler for a canonical CNF/free-AND counterexample. JSON API is input_count, or_count, operand_wire_lists (two prior-reference lists per OR), output_wire_list.

Format-compliant Program n k is a recursive type alias built solely from tuples, lists and Fin; compile emits one empty AND plus one binary AND per conjunction reference, one OR per program step, and recurses. Definitions compiled SHA dc9fc17b0b48ae7caa20f941e7a9949547133a90950b49f655a7b12b4556ccb5, preserved with complete log. An earlier custom-inductive definition snapshot is historical only and must not enter final proof.

quadratic_shadow owns Monotone2 and exact OR-set cardinality; proof_routes owns arbitrary-input semantics and embedded initial references. The JSON generator at scratch/canonical-witness-to-lean.py validates bounds and emits explicit Fin subtype constructors, so invalid reference numerals cannot wrap modulo the signal count.

Canonical compiler milestones: structural proof compiled clean, SHA55948041b48cd85be6c7a5b89d19794748dd01e2bf38342393a34f1dde851b8c, independently reviewed by proof_routes. Semantics compiled clean, SHA391d99f4fbf9025d469e3aac2d51c08542a120f083b3216b110be336435d2780, independently reviewed by quadratic_shadow. APIs compile_eval, compile_circuitFun, compile_circuitFun_map preserve arbitrary inputs and embeddings.

Cycle/K2,2 JSON control passed all16 inputs with legal compiler output and exact2OR count. SHA f6db999250439424594feb586cbadd3ab05b962775af30eaf5a51cc51f456220. This is a control, not a target counterexample. Generator preserved in results/orch/canonical-witness-to-lean.py.

Next performance helper: Nat bitmask evaluation plus a supplied intermediate-mask checker, to verify each OR once from literal prior masks. Counterexample agent owns exporting sample masks; geometry owns all468-row completeness; child owns generic mask semantic bridge. No concrete target counterexample is known.

Bitmask certificate infrastructure compiled and reviewed: canonical-compiler-mask-certificates SHA e6d6fb6f54e6e20749d632aeabf6098d940a1f09b091ebb496571d9f4b705795. It checks each OR mask against a supplied Nat literal and advances with the literal, then checks final conjunction. Generic sample wrapper SHA f0a32c04062e4e86770b14dcdea3b94bb04a9882d7182e2f976bd0c91e1a19b6 compiled and independently reviewed by or_lower_bound.

Counterexample exported a51-OR baseline (not a counterexample) and520 sample masks. Independent Python reconstruction from exact Lean Flags.flag/AllRows.row literals verified all13,520 coordinate bits; report canonical-sample-data-review.json. Literal-mask certificate, fixed sample data, and26 split negative-bit checks are prepared under compiler-prepared with explicit uncompiled labels. Root scheduled GeometryFlags/GeometryCompletenessProofs first, then the51-OR control and one finite input-bit benchmark.

All fixed520-sample masks are now kernel-certified: Bench checks1352 positive bits and468 negative coordinate0 bits; Remaining checks11700 other negative bits plus truth/result masks, exit0 in14.52s (11.4s kernel). Remaining SHA7b00692eb51856469bc6a9ae23fb753c497b0cc707d37ce5a94ad11c339da547. The51-OR literal-mask control passed3.50s, SHAc0521c306db3245beb24c28ed2812251e78e80313e5e198e22f882305aa00fb7. No≤50 witness is known. Geometry owns full8192-mask completeness; compiler process slot was released.

# S03 finite-boundary proof review

PASS: independent proof/data/format review of the compiling 40-input sufficiency helper. No blocker to the orchestrator publishing this compiled partial after the ongoing axiom audit. This helper does not prove or refute the posted 21-gate existential.

Reviewed at 2026-11-24T03:27:41.068983+00:00.

- Scratch source: `/tmp/oec/pequalnp-pilot-18/boundary-lean/Boundary.lean`, 148 lines, SHA256 `cfc466912c36549c3d1538d646ae9f1a5748e4e2f95dd8a70487d997cf957021`.
- Integrated source: `lean/PEqualNP/Outside/L_meta_1342.lean`, 2000 lines, SHA256 `f872b394be5f8fdcfd20fe735e26856aebdcc88b17a305f35a49a85d8a8fcfdb`.
- Hash-bound review: `/tmp/oec/pequalnp-pilot-18/orch/S03/boundary-review.json`, SHA256 `76571d29fa29fba47eecd301abac8bfbb6848c5097da2684c584e98ab9c0aaa1`.
- Replay script: `/tmp/oec/pequalnp-pilot-18/orch/S03/review_boundary.py`; successful full diagnostics: `boundary-review.stdout` and `boundary-review.stderr` in the same directory. Earlier review-script diagnostic files are retained separately.

The exact checked helper statement is:

```lean
lemma target_boundary_spec (C : Circuit)
    (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (positive : ∀ e ∈ targetEdges, C.eval (List.ofFn (pairBits e.1 e.2)) = true)
    (negative : ∀ T ∈ targetNegativeSets, C.eval (List.ofFn (boundaryBits T)) = false)
    (x : Fin 11 → Bool) :
    C.eval (List.ofFn x) = true ↔ edgeTrue targetGraph x
```

The 16 ordered edges equal the posted natural-number edge list. Independent enumeration of all 2048 assignments finds 125 independent inputs and 1923 positive inputs. The listed 24 negatives are exactly all maximal independent sets: 22 of size four and two of size three. Every independent input is contained in a listed negative set. All 40 test rows are distinct. The Boolean helper's 16 antecedent clauses and 24 conclusion clauses match these edges and complements in order, and its implication holds on all 2048 assignments. These independently recomputed results agree with Boyle's older static review and graph metadata; that older review described a different source hash and is not itself build evidence for this source.

The forward proof extends the support of a putative false positive to a listed independent set, then applies actual circuit monotonicity and the negative test. The backward proof raises a positive edge-pair input to the requested input, treating both orientations of targetGraph. There is no cleanliness, gate-count, well-formed-index, nonempty-input, or exact-two-wire premise. Monotone2 supplies AND/OR operations; the inherited evaluator argument handles constants, unary gates and default-false reads.

The scratch build record `boundary-lean/seventh-result.json` binds the source hash to exit zero; both full seventh logs are empty. The integrated named build has exit zero and successful build output with module-system warnings in `boundary-lean/named.stdout`; `named.stderr` is empty. The named result JSON itself stores exit code and elapsed time only: its source binding comes from the orchestrator's explicit hash confirmation plus this review's matching current bytes. No duplicate build was launched.

Integration is byte-for-byte the reviewed base plus the scratch declarations inserted before the final auxiliary-namespace end. The scratch Outside-module import and extra wrapper were omitted. All eight helper names are new relative to the reviewed base. The fragment uses only permitted scoped limit options and contains no prohibited proof mechanism, custom datatype/instance, strings or attributes. It introduces no additional namespace block. The pre-existing two helper namespace blocks and absent exact posted theorem remain final-submission issues tracked by S08; this review approves a research checkpoint, not final submission format. The orchestrator's transitive axiom audit is pending.

After reading the current shared notes, the next useful step is candidate proof generation: establish 16 positive and 24 negative evaluations for any concrete circuit, apply target_boundary_spec, and rewrite edgeTrue targetGraph to the exact oriented posted predicate. The finite-boundary proof is complete; more case-tree optimization is unnecessary for the current checkpoint. No BoundaryFix file or Lean worker was created, no named proof file was edited, and no git/network/desk writes were performed by S03.

## Candidate certificate scaffold, 2026-11-24T03:32:02.866966+00:00

Compiled `orch/S03/BoundaryFix.lean`, SHA256 `80802f27b96a4e01e5c4b2d54fe4aa4276adb84fe83a664d96e6ee5092cdbd53`, exit0 in5.79s, peak childRSS3267476KiB, both full logs `orch/S03/scaffold-second.stdout` and `.stderr` empty. Build/source binding: `scaffold-second.result.json`; exact statements: `scaffold-exact-statements.txt`. The source adds a closed40row Boolean checker, its equivalence to the two boundary premises, a bridge from symmetric targetGraph to the exact posted oriented natural-number edge existential, and a generic bound-parameter witness constructor. The known22 baseline passes the40row computation independently of baseline_spec, and the constructor establishes only the22 bound for that control. No21 witness is claimed. Scratch Outside import must be removed when integrating the body. Axiom audit is running next under the same Lean lock.

Scaffold axiom audit PASS: `scaffold-axioms.result.json` records exit0; full `scaffold-axioms.stdout` lists only propext/Classical.choice/Quot.sound or subsets. The computed `baseline_boundary_check` uses the same three permitted axioms; only the earlier `boundary_cover_bool` audit reported no axioms. The source hash above is unchanged.

## Reusable emitter and final scaffold handoff

The scaffold is complete. `orch/S03/candidate-scaffold-manifest.json` binds all source, exact-statement, full build/audit log and finite-control artifacts; SHA256 `fa23cf0b30a0c6e395243facf18cee76a0319f1b3c9b5db966e38e7e3879280b`.

- `BoundaryFix.lean`: SHA256 `80802f27b96a4e01e5c4b2d54fe4aa4276adb84fe83a664d96e6ee5092cdbd53`; 40-row checker, exact posted-predicate bridge, generic bound constructor, independently computed22 control. Compile exit0 in5.79s, empty logs.
- `GeneratedBaseline.lean`: SHA256 `4b51d55d13bb9b36cb131f61a6145469a543448c8baa279e1699e26faa94dbe8`; generated22 circuit and computed40row certificate. Compile exit0 in6.39s, empty logs. `GeneratedBaseline_certificate` proves the exact oriented target existential with bound22 only.
- Both separate axiom audits exit0. All six scaffold lemmas and both generated lemmas list only `propext`, `Classical.choice`, `Quot.sound`.
- `ProjectedScaffold.lean` is an uncompiled integration projection only. The actual repository plain/import guard passes; its final-theorem check rejects the missing posted theorem as expected. No named file was changed.

`emit_candidate.py` accepts JSON with `inputs:11`, `gate_wire_offset:11`, a `gates` array of `[op, input0, input1]` entries (zero/one-input variants and `{op,inputs}` records are also accepted), and an explicit natural-number `output`. It preserves original Circuit semantics, including zero-input constants and default-false unavailable reads. It rejects raw stochastic/SAT virtual-constant numbering; normalize that upstream using the existing reviewed validator. Before emitting, it checks all40boundary rows and all2048inputs. The emitted Lean proof recomputes actual Circuit.eval and applies the formal bridge; scalar success alone is never called a proof.

Example, using a fresh artifact name:

```sh
python3 /tmp/oec/pequalnp-pilot-18/orch/S03/emit_candidate.py /tmp/oec/pequalnp-pilot-18/orch/S03/baseline-control.json --name FreshCandidate
python3 /tmp/oec/pequalnp-pilot-18/orch/S03/run_lean.py FreshCandidate.lean fresh-candidate-build
```

All emitter outputs remain in S03 scratch. The runner holds the shared fcntl Lean lock and records complete diagnostics and source hashes, with a180s process-group timeout. Reusing an existing artifact name is rejected, so a failed later input cannot silently reuse an earlier Lean file. Wrong-output, offset13-numbering and reused-name controls all passed. The emitter was hardened for name freshness after the positive compile without changing source-emission or evaluator logic.

Only the22 baseline was supplied and proved. The next proof-generation step is to feed an independently validated normalized candidate to this emitter; a21-gate claim requires an actual passing candidate and its Lean compile. Any final proof file must inline required declarations, omit the scratch Outside import, and use the exact final theorem name/type. Main retains integration and publishing authority.

## Integrated-module emitter fix

S03 INTEGRATION FIX+NEW COMPILE: emitter SHA f0df2b3fbd6aaec3745c390f629022818e1c083c5824e05e31c59a528b492fd0 automatically detects all five integrated helper declarations, supports --helpers-existing/--helpers-inline, rejects partial auto-integration and _root_ names. Prior emitter preserved as emit_candidate.pre-integration.py SHA3a667... . Fresh IntegratedBaselineControl.lean SHAa0bd81e806d52a4ef6ce8ec48380f50b2558151bd487921296a643bbb5e3819e compiles exit0/5.90s under lock, full integrated-control.stdout/stderr empty. No helper redeclarations. Exact22-only existential in integrated-control-exact-statement.txt. Auto/existing equality and prior-inline fallback equality modulo names checked; root-name rejected; integration-emitter-controls.json binds checks. Fresh audit next; all prior artifacts preserved. Returning S05 algebraic route after packaging this fix.

## Independent2069-line checkpoint review

S03 INDEPENDENT METADATA/INTEGRATION REVIEW PASS FOR PROMPT PARTIAL PUSH: exact named2069 SHA0e0620c89307cf34be010940037cb187797eea76c85fc8c8a89b9bd1cfc56e5c is byte-identical to prior ProjectedScaffold. All9 checkpoint artifact hashes, validation SHA/current2069/partial22-only/checkerNOTRUN claims, source-bound named build0/57.96s and six-lemma axiom audit0/allowedthree verified; no concurrent changes/blocker. Review orch/S03/scaffold-checkpoint-independent-review.json SHA289ba6a7dde0eddd2462398061c0f35957c1b2671b45549963766b46a773af8c. No new build for review. Emitter fix already compiled fresh integrated22control; its completed fresh two-lemma audit also exits0 (integrated-control-axioms.*). Returning S05 algebraic route.

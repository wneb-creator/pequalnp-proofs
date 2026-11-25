# Independent preflight and semantics review

Reviewed upstream commit 2b3ba8b5 for gap L-meta-2592 on 2026-11-25.

## Submission and checker

- Current upstream supports reductions: `node tools/check-lean.mjs <file> <statement.txt> reduce`.
- Full file guard invocation changed to `node .github/scripts/outside-guard.mjs imports <source-file> <imports.json> <repo-relative-file> <check|refute|reduce>`.
- Gap guard supports `node .github/scripts/outside-guard.mjs gap <gaps.json> <gap-id> <repo-relative-file> <output-directory> reduce`.
- An ordinary proof must put all helpers inside its own module namespace (or that name with `_aux` suffix). The target theorem is at top level, fully qualified, and last. Namespace/section/end commands start at column zero; each end names its block.
- A reduction has exactly its one theorem, no helpers and no namespace. It has 2 to 4 independent closed proposition hypotheses. Its conclusion is checked by structural equality, stronger than definitional equality. Children must print to at most 2000 characters and cannot repeat, contain the parent statement, or be decidably false.
- The current lease record says `reductions_live: 3`. The user and join instructions cap a step at three live reductions. Therefore a fourth reduction is not permitted unless an existing one ceases to be live; `reductions: true` alone is insufficient. The local guard only checks `reductions: true`, so local acceptance would not establish that a fourth submission is permitted.
- A local `refute` check can validate the negation of the original statement. The public guard requires the desk's gap kind to agree with `refute`; proving the negation of a gap posted as an ordinary proof does not automatically fit its public submission flow.

## Circuit semantic audit

- `FanInTwo` genuinely restricts every gate to AND, OR, NOT and at most two listed inputs; MOD/MAJ cannot slip through.
- Evaluation is sequential fold-left appending exactly one Boolean for each gate. No cycles, aliases, mutation, implicit gates, or self-reference.
- Missing and future wire references read false. They only supply false constants; they cannot read a future computed value.
- Empty AND and empty NOT produce true; empty OR produces false. All such constant gates count toward size.
- NOT ignores its second input, so two inputs do not add expressive power.
- Size is the full gate-list length, including unused gates. The requirement that a NOT occur is syntactic and permits dead NOT gates, but this does not make gates free.
- The output may be any earlier wire, an input, or out of range; an out-of-range output is constant false. Reading an earlier wire merely makes later gates unused and still counted.
- Every truth-table input has length exactly ten. There is no varying input-length or index ambiguity to exploit.
- The target expression is the fifteen-edge Petersen graph: an outer 5-cycle, five spokes, and the inner pentagram. No obvious missing/duplicate edge or Boolean-precedence defect.
- No semantic counterexample or loophole found. A refutation still requires an actual circuit of at most nineteen counted gates.

## Final independent review checklist

1. Final PR diff adds only the named Lean file, mode 100644, UTF-8, at most 512 KiB.
2. Exact posted statement, fully qualified theorem name, namespace ownership, allowed imports.
3. No forbidden substrings in code, names, or comments; run the actual guard, including `_root_`, quotes, and attributes.
4. Pinned build configuration unchanged; no sorry, new axiom, native decision, or hidden helper dependency.
5. Final build and checker log correspond to final source bytes and produce ACCEPTED, not merely a successful Lean elaboration.
6. Branch, remote, lease, gap status, and reduction availability checked before submission.


## Existing-proof assembly audit

The initial 165-file Petersen inventory omitted some useful sources. Additional matching files are recorded in `/tmp/oec/pequalnp-pilot-111/petersen-more-files.txt`.

- `L_meta_4725` proves the binary-floor child of `R_meta_2592_271`: at least 15 AND/OR gates, with NOTs counted separately. It has 3224 lines.
- **`L_meta_6581` strengthens that floor to 16 AND/OR gates**, for every FanInTwo circuit computing the full Petersen function. It imports only Defs, has 4555 lines / 284540 bytes, and is therefore a viable same-file source transplant. Under size at most 19, any counterexample has at most three NOTs. The predicate `!g.op.eval [false]` equals true exactly for AND/OR among the allowed operations.
- `L_meta_8295` proves exactly the generic last-NOT cut child of `R_meta_2592_318`. The separator child remains the difficult statement.
- `L_meta_7389` proves exactly the normalization child of `R_meta_2592_408`. The normalized lower bound remains difficult.
- `R_meta_4727_17` separates semantic compilation with shared complemented signals from a finite-function lower bound. No solved lower-bound assembly found.
- `R_meta_4727_53` separates compilation into signed BinaryCircuit gates from a signed-gate lower bound. No solved lower-bound assembly found.
- `R_meta_4727_1` splits on whether a NOT occurs. Its solved child `L_meta_8021` is vacuous because it combines no NOTs with positive notCount. Its nonvacuous child is essentially the parent with a redundant hypothesis.
- `L_meta_5236` proves an initial-OR(0,2) case with suffix size at most 18 and 3–4 NOTs, under ReadsBack and generated-output bounds. `L_meta_5238` covers at least five NOTs for that suffix. Neither is a universal Petersen bound.
- `L_meta_5367` proves that an initial-NOT(0) suffix has size at least 15 plus the number of its effective readers of input 0 or its complement. This reduces size-19 candidates to at most three such readers; a core case remains.
- `L_meta_4332` excludes a wire (or its complement) of a size-at-most-15 circuit on the nine-vertex restriction x9=false. It can support elimination arguments, but does not by itself eliminate four gates of an arbitrary size-19 circuit.
- `L_meta_10792` is not general single-NOT elimination. For one particular seven-input graph, it proves a ten-binary-gate floor and substitutes a fixed eleven-gate monotone witness whenever a NOT occurs. The at-most-one-NOT hypothesis is unused there. Its argument cannot directly give Petersen monotonicization.
- `L_meta_1755` is a checked concrete twenty-gate monotone Petersen witness.

No complete proof of L-meta-2592 can presently be assembled from the inspected solved statements alone. The strongest direct progress is the sixteen-binary-gate floor, reducing the unresolved search to one, two, or three NOTs. All inspected external proof arguments must be copied and renamed under L_meta_2592's own namespace, because the lease permits no outside imports.

## Independent research checkpoint reviews

These approvals concern preservation of compiled research components on the pilot branch. They do not approve a proof PR or claim the posted theorem. Owners reported successful Lean exits, and the complete successful logs were checked for errors. Each source was frozen for review; hashes identify the approved bytes. Forbidden-marker scans found no sorry, admit, new axiom, native_decide, forbidden root qualifier, string literal, or non-simp attribute.

| Component | Lines | SHA256 | Exact scope |
| --- | ---: | --- | --- |
| Certificate.lean | 2235 | `279dc52f703612030973e13312c1cebddb0a6452b4987b681c46fa61940cc541` | Kernel LRAT soundness and circuit-to-normal-CNF model; no UNSAT certificate. |
| Negation.lean | 113 | `7f29f84a58d321a86f16702a66ec649a145c94a298d534333d17e7123524875e` | Semantic constant substitution and Petersen boundary masks; no circuit-size preservation claim. |
| GateElimination.lean | 32 | `c7d612ecf0b76944d2afa21d61183691ba336254ca15b5bcb927902907c186c9` | Every variable remains essential after fixing a distinct variable; no gate deletion theorem. |
| RetentionWitness.lean | 44 | `6aef0366f0f350b87e5549e3cf1688ffddafb01ad8eec4790479f9e812ec8464` | Finite row witnesses force retention of either first-gate input; no binary-count conclusion alone. |
| CertificateCount.lean | 2283 | `6d9bdceb862b89c287139b358c45aceda0ae252b6c3c44493b47048b893d0ae7` | Exact NOT count after bypass/delete normalization and operand swap. |
| CertificateBound.lean | 2474 | `adc27bcc172c4ded1b90154e442678d21ba54d0eba6f4db83947cb161f8e254f` | Adjacent independent-gate exchange preserves NOT count; normal-form existence retains a NOT-count upper bound. |
| Geometry.lean | 47 | `ca1c66e341e8400f4ffaa3a75e23e979c699d9bcf5590eb55a4c222813cc0bd9` | Ten finite projections give the nine-vertex target, supply its inputs, and kill the selected vertex. |

The Certificate extensions contain their previously reviewed versions as exact prefixes. Certificate's custom inductive/structure declarations remain a final-PR fast-path/manual-review caveat. Geometry's four concrete inputs/graph/pins/target definitions exactly match CombinatorialStrong.

## Seventeen-gate argument audit

The proposed Seventeen argument is semantically sound at the reviewed draft level. `Live` permits retaining either operand in its `U` set. The finite row witness forces the selected raw input to remain there. `list_run` preserves this fact through explicit retention flags and uses a list with distinct original signals. After fixing that input false, `projected_bound` charges its constant occurrence in the projected list, giving fifteen plus one at most the remaining binary gates, hence seventeen in total.

The proposed eighteen-gate refinement for a first AND or signed difference may charge both the retained input and the fresh first-gate output after fixing an annihilating input false. They are distinct before projection and both constant afterward. This uses the proved constant mass invariant. It does not assume a generic charge for duplicate nonconstant projected signals; that stronger invariant is unsound for signed selectors. The first-OR case obtains only the single constant charge by this argument. Compilation and final-byte review of the completed lower-bound file remain separate requirements.

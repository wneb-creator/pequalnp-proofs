# Independent review by checker_review

Reviewed UTC: 2026-11-25T01:10:47.149836+00:00

## Scope and status

Static review only. Lean compilation and local checker have not yet run because project artifacts are being prepared. This review does not claim the posted gap is proved.

## Conditional normal form

File: results/orch/lemmas/normal_form.lean
SHA256: 2b53479031c968b45e1d0e0c48fd2ff1525641757538e6e8da994ef654bb6bbe

- Cleanup helpers and final cleanup lemma match upstream L_meta_1906 after namespace changes and changing helper declaration keywords to lemma.
- The sound_reduction proof matches upstream R_meta_1031_2.
- The final conclusion equals the posted L-meta-1031 statement exactly.
- The final theorem still assumes existence of a semantically sound size-minimal circuit for every relevant graph. This is the unresolved mathematical premise. The file is a conditional partial; it cannot be submitted as a full proof or as a valid reduction with only one hypothesis.
- A top-level namespace opening was added after review found that the final statement used names whose previous opening had ended with the helper namespace.

## Other partial files

- checker_review.lean: the two-AND chain computes a single-edge graph, both gates are pivotal under replacement by false, and the final gate owns no pair. The circuit is nonminimal; this is not a refutation of the posted theorem.
- boundary_certificate.lean: a monotone Boolean function agrees with the graph edge function if it accepts each edge pair and rejects every maximal independent set. The mathematical argument extends any independent support to a maximal independent set and uses monotonicity.

## Static checks

The discovered results files contained no credential-shaped matches. The three Lean files contained no forbidden constructs, double quotes, prohibited attributes, or forbidden name fragment. They are ordinary text files below the size limit. No proof/source file outside results has been changed at review time.

Any PR still requires exactly the named single file, an unconditional theorem with the named module, successful build/checker, and a fresh review of the final diff. The results artifacts are suitable for preservation on the work branch only.

### Independent review by normal_form: compact_or scaffold (2026-11-25T01:35:14.496268+00:00)

PASS. SHA256 2a5b62b625ec0221e80de3189dac274a8fe43756685b4d20371d0e42ba617c83. Definitions implement ORs of conjunctions over prior atoms; list identities preserve bounded atom reads and wire lengths. No translation theorem or OR lower bound is present, and no such claim is supported. Static format checks clean. Empty meets evaluate true and unbounded atoms false; a later well-formed translation must handle constants, or use the proved minimum-circuit strict-binary normalization to avoid them.

### Independent checkpoint documentation review by normal_form (2026-11-25T01:36:28.874639+00:00)

PASS. The public gap metadata has no lease/token/authorization fields, and the preserved statement exactly matches the original desk statement. README and compact validation clearly state scaffold/conditional status, with the main gap unproved and no proof PR. Dated notes and timeline retain historical pending statuses rather than claiming those were final outcomes. Axiom audit is explicitly snapshot-scoped. Sensitive-pattern scan of the nine new text/JSON documents found no matches; no lease identifier or credential is included.

### Independent complete compact translation review by normal_form (2026-11-25T01:37:48.820913+00:00)

PASS. File 247 lines, SHA256 8bf11c21c3a292793a74e48bdb9c8fed3ebe1de94e3fe6aa2274f50b78b76b46. The representation invariant equates every original wire with a bounded conjunction of compact atoms on every input of length n. AND concatenates representation lists; OR introduces exactly one atom and preserves all prior bounded reads. The final theorem explicitly requires normalized binary backward-reading gates and a valid output, then preserves evaluation and exact OR count. No lower bound or full-gap result is claimed. No BV/native/reflection escape, forbidden declaration, or additional axiom appears in the source.

### Independent compact padding and mask review by normal_form (2026-11-25T01:42:38.071725+00:00)

PASS. Source353lines, SHA256 ea60538c38f94b174ad1b7282827bafac237c14689a60b8e49ca56585f59171e. Appending unused OR(x0,x0) preserves bounded outputs under n>0. Conjunction evaluation is insensitive to order and duplicate indices, and mask8 stores membership bits7through0 with matching getLsbD indexing. All bounds needed for reads and padding are explicit. No native/reflection trust escape appears.

### Independent compact vector and conditional-bound review by normal_form (2026-11-25T01:46:31.971578+00:00)

PASS. Source508lines, SHA256 93b666ef9bfd0eba9b6a7ee1655235ca341be2a1e626aff9be55409165def89a. Vector operations project to Boolean evaluation on each of ten bits, and bounded atom lists convert correctly to8-bit selection masks. cycleInputs columns0through4 are C5edges01,12,23,34,40; columns5through9 are nonedges02,03,13,14,24. circuit_four_ors assumes the explicit FiniteObstruction premise and the ten test values, pads to exactly3OR, and derives a contradiction. The finite obstruction is NOT proved in this file, and no unconditional lower-bound or full-gap result follows yet. No native verifier, added axiom, or reflective trust escape appears.

2026-11-25T02:22:26.394030+00:00 — graph_ownership independently reviewed first_or_reduction.lean839lines SHA6fde7a84ee5c2c47a0f8361965325e21421ba5a906e4a914de20eb6650960e20: PASS. Compile exit0, three new theorem axioms standard only. Explicit limitation: at most one distinct original input per first operand; empty/equal-literal cases not yet excluded.

2026-11-25T02:24:18.081194+00:00 — graph_ownership independently reviewed first_or_reduction.lean970lines SHA0b9e93d247249dc315c0e761df83eaf3e9c6b2a3bd0659adf5264caa29542225: PASS. Reviewed839-line prefix unchanged; new domination helper correctly parenthesizes Boolean disjunction; empty/equal-literal cases eliminated. Compile exit0 and all three new theorem audits use only allowed standard axioms.

2026-11-25T02:26:22.966830+00:00 — normal_form independently reviewed final root search archive: PASS. root_signed_search.py SHA f2a5f77175662a27cf7636cf2b0beac14e4a87dac9dd99c92db14b7878d3967d implements earlier-atom signed domination in the correct directions P(v)⊆P(w), N(w)⊆N(v). Exact-count/no-padding labels prevent unsupported at-most claims. The inherited padding-pair existence guard imposes no extra solver constraints and is satisfied in the tested graphs. root_followup_search.py SHA f3c0afbf19bc1b03a232ba04591871b6536ddfc0ed6e36b4c9b2cba3f664e38f calls the intended freeAND and full-gate unsound-AND APIs. Independently replayed the signed C5 SAT witness on all32 assignments with zero errors. All7 signed result rows and2 follow-up result rows equal their complete stdout rows; both stderr files are empty. Signed results JSONL SHA c095d8ef87d64ff179cfe1041ab63fa6414a8683e44bccc95850bc44d1f4f242; follow-up results JSONL SHA eb244fa625e333e9b5a4f0801d2fe3223162c98f70cd29e655f2e789a66d64a9. Timeouts remain UNKNOWN; no certified lower bound or full-gap result is claimed.

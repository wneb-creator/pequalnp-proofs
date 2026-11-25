# Independent review: UpstreamDagTools

Verdict: PASS for exact reuse of the generic upstream framework, with
the conditional scope described below. No 24-gate construction or
unconditional 25-gate lower bound is established by this module alone.

The reviewed module is 3,470 lines and 161,586 bytes, SHA-256
`9b40c5b76e8629258e9e066712c57e5aa98fc72b16e223f170ff09e9ed4a629a`.
I used an authorized read-only `git show` to verify the source at commit
`790ef40780fc680c09cde228f2229fe058bd6e08`, path
`lean/PEqualNP/Outside/L_meta_9774.lean`. Its bytes exactly match the
archived upstream file, SHA-256
`520735eab64913c4e1c8d0146abec81ef2c08c8a825a2c98b92f7dc86cd1454d`.

An exact programmatic comparison confirms that the new module is the
first 3,468 lines of that source, with only the outer namespace changed
and its closing command appended. No theorem statement, hypothesis,
definition, or proof in that prefix changed. The comparison and scan
results are preserved in `upstream-tools-independent-validation.json`.

The source imports only `PEqualNP.Defs`. It has no `sorry`, axiom
declaration, `native_decide`, unsafe declaration, forbidden root marker,
string literal, or option. Its only attributes are two `simp`
attributes. Both complete archived tool-check logs are present and
empty; the provenance record reports compilation and export exit 0.
I did not rerun the build or claim a separate printed-axiom audit of
every imported theorem. The reused module introduces no new axiom.

I inspected the normalization definitions and main proofs. The DAG
encoding uses `true` for AND and `false` for OR; this differs from the
integer operation codes in the stochastic search. `Strict` requires two
distinct earlier wires. `Live` requires every input and every non-output
internal wire to have a reader. Readers count gates rather than input
arcs, and distinct operands are what make the arc/fanout count exact.

`exists_strict_of_monotone2` explicitly handles constants, input
projections, and otherwise a nonempty strict DAG. Its reference map
models default-false unavailable reads, nullary constants, unary copies,
and idempotent equal-input binary gates; no strict-input assumption is
silently imposed on the original public circuit. Output selection is
truncated to the actual output gate, preserving semantics and size.
`normalize_strictLive` additionally requires nonconstancy, exclusion of
each input projection, and essentiality of every input. These are real
premises, needed to remove unused internal gates and to rule out unused
primary inputs. They must be discharged for the exact graph target by a
separate application.

`surplus_identity` is correctly restricted to `StrictLive` and gives
`totalSurplus + n = D.length + 1`. The split into `Bplus` and `Bzero`
uses whether a wire is true on some singleton input, not arbitrary
functional dependence. The counting proof accounts for two arcs per
strict gate and one necessary reader for each non-output wire; natural
subtraction is protected by liveness.

The graph semantics `sem_Comp` quantify over every Boolean assignment.
`sem_Gr` explicitly assumes symmetry, no loops, separation of the open
neighborhoods of distinct vertices, and a neighbor different from any
specified vertex. It is stronger than merely being a simple graph.
The first-branch/pure-support and ineligible-vertex conclusions retain
these hypotheses together with strictness and exact target semantics.

The later flow, support, and charging results remain conditional. For
example, `sup_charge` assumes a chosen support set of size at most seven,
specified occurring triples, and pairwise intersection restrictions;
`sup_count` assumes explicit witness assignments and singleton cases.
`k4_budget` assumes `StrictLive`, `sem_Gr`, exact graph semantics, and a
pure-branch assignment. It does not itself supply graph-specific finite
budgets or a final circuit lower bound. The final generic sections close
before the adapted graph data, which is being reviewed separately.

The module is reusable checked infrastructure. A final single-file
submission still needs the exact graph application, the posted result,
and the repository's final checker verdict.

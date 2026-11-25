# Exact refutation packaging: read-only checker findings

No certificate of at most twelve clauses was obtained in this session. No target checker was run. The best completed Lean certificate has fifteen clauses. The instructions below record the inspected checker contract for any future successful candidate.

The recorded statement in `statement.txt` is a negated existential: there is no PHP(5,4) RUP refutation of length at most twelve. In `refute` mode, `lean/CheckLemma.lean` line 473 constructs `Not recorded` and asks the kernel to use the named theorem at that exact type. Therefore the final theorem must prove the double negation of the existential. A theorem whose type is merely the positive existential is not definitionally equal to this required type, despite the easy logical implication.

The final declaration must be named `PEqualNP.Outside.L_meta_9248` and have the form:

```lean
theorem PEqualNP.Outside.L_meta_9248 :
    ¬ (¬ (∃ ρ : List (PEqualNP.ProofComplexity.Clause (Fin (4 + 1) × Fin 4)),
      PEqualNP.Search.IsRUPRun (PEqualNP.ProofComplexity.PHP (4 + 1) 4) ρ ∧
      (∅ : PEqualNP.ProofComplexity.Clause (Fin (4 + 1) × Fin 4)) ∈ ρ ∧
      ρ.length ≤ 12)) := by
  intro impossible
  exact impossible verifiedWitness
```

Here `verifiedWitness` denotes a proved helper existential, not a placeholder permitted in a real submission. `RUPHarness.validated_refutation` yields that existential after the candidate replay, empty-clause membership, and length bound have all been kernel checked. The harness, candidate data, and proofs must be inlined into the one named file. Only `import PEqualNP.Defs` is necessary; remove all development-module imports. Helper declarations remain within namespaces below `PEqualNP.Outside.L_meta_9248`, and the fully qualified final theorem stands last outside those namespace blocks.

The exact local checker invocation, from the repository root, is:

```sh
node tools/check-lean.mjs lean/PEqualNP/Outside/L_meta_9248.lean \
  results/orch9248/statement.txt refute
```

Preserve the original posted statement file. Do not replace it with its negation; the `refute` argument performs that operation inside the verifier. The script returns zero only on acceptance; exit one means rejection, while exit three means checker fault and is not a proof verdict. Capture complete stdout and stderr. Root owns the named-file build, lease renewal, checker invocation, and publication.

## Authoritative intake caveat

Local checker support for `refute` is not sufficient to establish that a particular PR will be routed to that mode. `.github/scripts/outside-guard.mjs` lines 159–163 requires the public desk row's kind to match the requested mode. A missing `kind` defaults to `check`. `.github/workflows/authoritative.yml` lines 146–162 explicitly enforces that match before the proof is built. The saved desk response for L-meta-9248 omits `gap.kind`; that response alone does not establish the kind of the separate public feed row.

The saved `join.txt` also says that a counterexample can be sent through a posted negated twin. Before an eventual PR, verify the live public row or its negated-twin route. This is a documented routing uncertainty, not an automatic approval rejection. No request to change a desk row, no external write, and no PR was performed during this inspection.

## Final-file checks

The committed contribution rules require one new plain UTF-8 Lean file, at most 512 KiB; no forbidden substring, string literals, admitted proofs, new axioms, native decision procedure, or compile-time command; only allowed per-declaration limit options; and the exact theorem name/type. The small reflective checker uses ordinary Mathlib types and needs no custom data type or instance. Candidate data are integers and lists. Once a genuine at-most-twelve certificate exists, the final assembled file should be small compared with the size cap.

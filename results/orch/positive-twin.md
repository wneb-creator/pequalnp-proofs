# Positive twin review for L-meta-13154

Reviewed on 2026-11-25. Source: MiguelTorresPerez, public PR
https://github.com/open-goat/pequalnp-proofs/pull/17278 (L-meta-13153),
head `de537b761385fb944121cf601d95681e881d23ac`.
The PR was OPEN with no status-check records returned. Its author claims a local build;
this review has not independently Lean-checked that claim.

The source adds one 1,368-line, 59,037-byte file and imports only `Mathlib` and
`PEqualNP.Defs`. Its final theorem's type is byte-for-byte the inner proposition of
the assigned statement `¬ (...)` of L-meta-13154. Thus a valid proof of the PR's
theorem refutes our assigned statement.

## Mathematical route

- Normalize Boolean functions by their value on the all-false input. AND, OR, and
  directional difference generate normalized straight-line programs; NOT consumes
  no normalized binary operation.
- Turn a circuit into such a program, counting only non-NOT gates.
- Eliminate variables by restrictions, charging one or two binary operations.
- For this truth table, both restrictions of input 5 reduce the required normalized
  bound to six; further restrictions reduce to 3-input majority.
- The finite majority calculation shows normalized programs need at least four
  binary operations. The resulting six-input lower bound is eight.
- An explicit 9-gate monotone circuit computes the target. A circuit containing a
  NOT needs at least eight other gates, so this witness is no larger. A circuit with
  no NOT is already monotone and is reused directly.

Independent Python finite checks found that majority truth table 232 is unreachable
in zero through three AND/OR/difference operations from [0,170,204,240]. Numbers of
canonical states were respectively 1, 12, 114, 994. Direct evaluation of the nine
monotone witness gates gives 18369900215343697096, exactly
4277075690 * 2^32 + 4277062856. These checks support the route but are not substitutes
for Lean checking.

## Review and candidate

The current repository's full outer import/plain-file/namespace guard accepts the
original PR source. No declarations of new instances, structures, axioms, unsafe
code, prohibited options/attributes, string literals, or forbidden identifiers
were found. The proof uses `decide +kernel` for finite calculations. The final
statement explicitly names the project definitions and adds no hypotheses.

`results/orch/lemmas/Refutation.lean` is the candidate (1,309 lines, 55,497 bytes):

1. Rename the original namespace from L_meta_13153 to L_meta_13154.
2. Remove comments and collapse blank lines without changing proof terms.
3. Move the original positive theorem inside the namespace as `positive`.
4. Add the final theorem `PEqualNP.Outside.L_meta_13154` with type
   `¬ (the assigned statement)`, proved by applying the assumed assigned negation
   to `positive`.

The full outer guard accepts this candidate when supplied its intended PR path
and kind `refute`. It has not yet been built. Original downloaded source and
GitHub response are under the job scratch directory. Attribution must remain in
the eventual results or PR description if this proof is reused.

## Submission limitation

The assigned desk row has the default proof/check kind, not refute. The
authoritative guard refuses an explicit refute run when the posted kind is check.
Therefore a local `ACCEPTED (refute)` would establish the assigned statement is
false and justify preserving the artifact, but would not by itself make this an
accepted exact-statement proof PR.

The official script supports `next --proof-of L-meta-13153`, which requests the
positive twin using `gap=L-meta-13153&have=proof`. After preserving the result and
releasing only our own negative lease, root may request that positive twin with
the required `another=1&hard=1` flags. Only if the desk grants it is an exact positive
proof PR authorized by the site's lease rules. No desk requests were made by this
reviewer.

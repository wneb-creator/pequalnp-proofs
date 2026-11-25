# L-meta-2732 deliverable review

Reviewed 2026-11-25 UTC by repo_review. No desk calls, git writes, builds, or concurrent cache commands performed.

## Current assignment and reduction eligibility

The assignment is L-meta-2732, ordinary check kind (no refute kind is present), file lean/PEqualNP/Outside/L_meta_2732.lean, imports only PEqualNP.Defs besides Mathlib. Its theorem must prove the exact existential statement: two binary monotone prefix gates with ordered inputs and a symmetry-minimal rank, followed by a monotone residual circuit of at most24 gates, computing the specified Heawood edge function on all14-input assignments.

The row says reductions:true and reductions_live:3; the response also says reductions_open:true. All three reduction files already exist on the current upstream base: R_meta_2732_3.lean, R_meta_2732_427.lean, and R_meta_2732_773.lean. Therefore the user rule allowing at most three reductions per step is already saturated. Treat generic reductions_open:true as capability information, not authorization for a fourth reduction. A fourth reduction is not an eligible fallback under the present brief.

## Existing structure

- R_meta_582_773 is the checked parent cut that generated this target. Its search hypothesis matches L-meta-2732. Its second hypothesis prepends the two gates and is sibling L-meta-2734, already present in upstream.
- R_meta_2732_427 separates generic canonical-prefix normalization (for any14-input circuit) from synthesis of a well-formed AO2 circuit with26 gates.
- R_meta_2732_773 additionally separates extremal-row interpolation, leaving synthesis on minimal true and maximal false rows.
- R_meta_2732_3 supplies a finite65-prefix rank table, packed boundary truth-table columns, packed gate encoding, a decoder obligation, and a packed24-gate tail search obligation. These can guide local work, but none may be imported by the final file: the assignment only permits PEqualNP.Defs. Necessary lemmas must be reproduced inside the assigned file.

## PR census

Parsed the saved open-prs.jsons as12 complete JSON array pages,1185 entries total. No entry contains2732. The desk assignment independently reports pr_open:0 and empty pr_numbers. No new census requested.

## Valid result paths

1. Full proof: exact assigned statement in L_meta_2732.lean, no unsupported extra assumptions.
2. Refutation: mathematically valuable, but ordinary check assignment cannot be silently switched to refute. The current outside guard requires submitted kind to match the public gap row. An official negated twin or refute row must be identified before claiming checker-accepted submission of a negation. The local checker can test refute mode, but that alone does not make a PR admissible.
3. Partial lemmas: user requires early branch pushes as preservation. Label them partial honestly; they do not solve the assigned statement or qualify for a proof PR by themselves.

## Build and checker plan

Compile focused proofs first with PEqualNP.Defs and any necessary narrow Mathlib imports. No Defs source directly imports all Mathlib. Prepare the whole Mathlib cache only when a candidate is mature enough to need tools/check-lean.mjs; that checker always imports the entire Mathlib statement environment and cannot be made targeted without changing the trusted checker, which is forbidden.

The installed toolchain occupies3.1GiB. Cache CLI/leantar have no artifact-filter option. Sequential complete get batches followed by clean! can lower compressed-archive peak space but cannot lower final extracted requirements. Preserve private/server oleans and IR. Full checker disk feasibility remains unresolved; do not promise it before the cache exists.

Before final push: independent format review, scoped helper namespace, final fully qualified theorem last, exact statement, no forbidden text, permitted imports, named file only in eventual PR diff; build plus checker plus outside-guard. Keep results records on preservation history only if the eventual PR diff still adds exactly one Lean file.

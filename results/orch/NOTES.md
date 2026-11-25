# L-meta-2583 orchestration notes

Assigned gap: L-meta-2583. Exact statement in /tmp/oec/pequalnp-pilot-137/statement.txt. Allowed project imports: PEqualNP.Defs. Desk terms reductions_open=false, kind=prove. Helpers must live in the module namespace; theorem full name at top level, last. Parent owns desk calls and notes updates.

Strategies: proof_route (existing facts), counterexample (definition/small-case checks), combinatorial_route (lower bounds and star covers), intake_review (checker/formal constraints).

## 14:44 UTC findings

- ReadK.IsReadK 1 is one proof tree per prime implicant with each variable read once; it is not global syntactic read-once.
- Exact known construction: read1 incidence circuit D of size N*(q+2)-1. L_meta_2393 upper helper and L_meta_7684 general star-cover construction.
- Missing mathematical step: unrestricted AO2 lower bound N*(q+2)-1 <= C.size. Existing read2/read3 lower bounds are insufficient.
- No obvious malformed hypothesis; incidence conditions yield a projective plane.
- No open PR matching 2583 in census of 954 open PRs.
- Environment lacks advertised Lean/cache; parent installing isolated elan under scratch.
- Counterexample agent searching Fano circuits of size26 against 21 edge-true and 37 maximal-false test assignments.

## First compilation

The 659-line upper-bound construction and conditional normalization helper compile with Lean4.36.0. The target theorem is absent, so this is a partial result only. Exact Z3 Fano26-gate search is running; fixed27-gate sanity model verified on all16384 assignments.

## Dirty-gate obstruction

A five-gate AO2 circuit for a three-edge path is a lift fixed point but fails read1. Bypassing its dirty AND changes the function. A four-gate read1 circuit computes the same function. The finite example and general Boolean factoring identity compile and were independently checked. This is not a counterexample to L-meta-2583, and no saving is asserted in arbitrary shared contexts.

## Semantic frontier

New compiled helpers show that every true circuit input contains a prime implicant, and that a monotone function below the circuit function agrees everywhere if it accepts every prime. This proves the semantic half of deleting a gate that contributes to no minimal true input; constant propagation remains separate.

The dual compiled helpers show every false input extends to a maximal false set, and agreement there determines any monotone upper function. Together these give the semantic justification for forcing a gate to zero or one when it is irrelevant on the corresponding boundary.

## Constant folding

The generic constant-folding pass compiles with a standard Bool-sum-Nat wire status. Its invariant preserves each wire value and bounds emitted gates by old gates. This partial still permits NOT; preservation of the exact AO2 model and strict forced-gate deletion are separate pending lemmas.

## First strategy review

Broad source searches found no unrestricted sharp plane bound. Continue exact Fano synthesis with independent encodings and formalize the useful-gate/normal-form route. Do not assume all minimum circuits are read1: a minimum P4 circuit disproves that stronger claim. Reductions remain closed for this lease.

The constant-folding extension now proves AO2 gate-list preservation: emitted gates are binary AND/OR with backward references. Output selection and strict gate deletion remain pending.

## Lease interruption

A renewal succeeded at15:04:54UTC, extending expiry to15:24:53UTC. At15:05:21UTC the desk instead reported no live lease; curl-si confirmed HTTP410. All agents stopped. No proof or refutation was obtained. The original target remains absent, and the exact checker verdict remains REJECTED(no-theorem). Already compiled strict gate-deletion and forcing-semantics lemmas are preserved.

Search archive: three heuristic runs performed8967290883mutations and all stopped at one incorrect characterization test. Both unrestricted26-gate SMT encodings timed out with UNKNOWN; pruned variants were interrupted after lease HTTP 410. SAT controls at27gates passed exhaustive16384-input validation. Complete sources, solverinputs, statusrecords and logs are underresearch/.

## Final stop

The user-directed 410 recovery and one already-held retry both returned the same pre-existing L-meta-2590 lease, issued before our request, with the exact note: you hold 5 gaps, the most one handle may hold at once; release one to get another. That lease was not worked, renewed, or released. All L-meta-2583 compiled components and research files had already been pushed before recovery. No PR was opened, because the posted theorem is not proved. There were3 desk-next requests and0 nulls.

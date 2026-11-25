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

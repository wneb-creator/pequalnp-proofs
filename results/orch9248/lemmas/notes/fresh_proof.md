# Constructive RUP notes for L-meta-9248

Status: no proof of the posted lower bound and no run of length at most twelve.
The exact schemas below were checked with the finite unit-propagation checker,
not with Lean. They are useful candidate families for the other search agents.

## Definitions and scope

The posted formula has five positive pigeon rows and forty negative collision
clauses. It has no clauses forbidding one pigeon from occupying two holes.
Consequently, assigning a pigeon to one hole does not force that pigeon's other
coordinates false. Any Hall-sharing argument must respect this point.

The RUP definition requires a falsified clause from the current database under
the complements of the proposed learned clause. Its inductive propagation
relation is finite. I found no logical loophole in this definition.

## Hall schemas

Let S be a pigeon set and H a hole set, with |S|=|H|+1. Let

    E(S,H) = OR { x[p,h] : p in S and h outside H }.

Every displayed sequence is chronological. Literal polarity and unit hints are
saved in hall_schemas.json. The script hall_schemas.py checked all ordered
instantiations: 80 for Hall2, 720 for Hall3, and 2880 for Hall4.

### Two pigeons and one hole: one clause

Learn E. Negating E forces both pigeons into the remaining hole and conflicts.

### Three pigeons and two holes: two clauses

Write S={a,b,c}, H={h0,h1}. Learn

1. E OR NOT x[a,h0].
2. E.

For the first clause, its negation puts a in h0 and forces b,c into h1.
For the second, the first clause forces a away from h0, hence into h1;
b,c are then forced into h0. The schema costs two clauses, not three.

### Four pigeons and three holes: five clauses

Write S={a,b,c,d}, H={h0,h1,h2}. Learn

1. E OR NOT x[a,h0] OR x[c,h1].
2. E OR NOT x[d,h1].
3. E OR NOT x[b,h0].
4. E OR x[b,h1].
5. E.

After assuming E false, the conflict chains are:

1. a=h0 and c!=h1 force c=h2, then b=d=h1.
2. d=h1 forces c!=h1, then clause1 gives a!=h0; a=h2, b=c=h0.
3. b=h0 and clause2 force d=h2; a=c=h1.
4. b!=h1 and clause3 force b=h2; clause2 then forces d=h0; a=c=h1.
5. clause4 gives b=h1; clause1 gives a!=h0 and hence a=h2; c=d=h0.

The existing checked twenty-clause PHP5,4 witness consists of four guarded
copies of the five-clause PHP4,3 proof. It replaces E by a negative placement
guard for the remaining pigeon; the last guard can be replaced by the empty
clause using that pigeon's original row and the other learned guards.

## Search implications and obstacles

The Hall3 and Hall4 schemas include wide clauses beyond the short initial pool.
Pure positive Hall clauses do not initiate propagation at the empty assignment;
conditional clauses or units must connect them to the final conflict.

Three asserted placements in distinct holes already cause an initial UP
conflict, even if some asserted placements use the same pigeon. Mixed signed
three-literal clauses can also be initial RUP: two placements occupy two holes,
a negative assumption in another pigeon row forces its remaining placement,
and the two remaining pigeons collide in the fourth hole.

Deriving both row-at-most-one constraints for a selected pigeon can improve
propagation, but such clauses are learned information and cannot be assumed
for free. I found no cost-saving complete construction from this observation.

The tiny exact minima PHP3,2=2 and PHP4,3=5, together with the posted but
unprovided thirteen-clause upper-bound claim for PHP5,4, make thirteen a
plausible optimum. This is a heuristic, not an argument for the target.

The general variable-query safety game cannot establish the requested bound:
an adversary can interrogate rows in 3+2+1 queries and force unit propagation.
The lower-bound agent independently identified this limitation and is using
the stronger finite-clause admissibility method instead.

## Final strengthening observation and freeze

The first Hall3 clause can be strictly strengthened by omitting a's outside-H
positive literals: retain NOT x[a,h0] and only b,c's four outside literals.
Under its complement, a is already placed at h0 and only b,c's rows are needed
to reach the collision. The first Hall4 clause can similarly omit a's single
outside literal. Later guarded clauses cannot automatically drop their guarded
pigeon's outside literals because earlier learned clauses may depend on them.
These strengthened variants were reasoned through but not added to the finite
all-instantiation checker before the freeze.

Root reported lease HTTP410 at 2026-11-25 17:14:26 UTC. All work stopped on
receipt. A thirty-second random greedy clause-strengthening pass was started
immediately before the stop message and interrupted with exit130. It reported
no improvement and produced no run artifact. Its script strengthen_runs.py is
preserved as unvalidated search code. No jobs remain active from this agent.

The successful preservation artifacts are fresh_proof.md, hall_schemas.py, and
hall_schemas.json. The Hall checker exited0 after checking all3680 ordered
instances. No new Lean source was authored by this agent for this gap.

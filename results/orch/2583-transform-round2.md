# Second transformation round

## A sound local star enlargement

Fix a line l and two sets A,B of point inputs. Let U_A and U_B be their ORs. If the wire x_l AND U_A AND U_B is below the incidence function on every assignment, then A is contained in the neighbors of l or B is contained in the neighbors of l.

Proof: otherwise choose a in A and b in B, both nonincident with l. The assignment with exactly point a, point b, and line l true makes the wire true while incidence is false. The case a=b is included. This statement needs no plane axioms.

Consequently the three-factor wire can be enlarged to x_l AND U_A or x_l AND U_B while staying below incidence. In a monotone circuit that already computes incidence, replacing an intermediate wire by a pointwise larger function that is still below incidence preserves the output: on false inputs both old and replacement values are false; on true inputs monotonicity prevents losing the old output. This handles a local family of repeated-leaf blocks.

## Why this does not finish normalization

The local replacement needs the relevant OR wire to remain available. General blocks can contain nonlinear children and can share both children elsewhere. The identity (p OR A) AND (p OR B) = p OR (A AND B) uses two gates instead of three only when at least one old OR child can be deleted. If both old OR children have other readers, replacing only the final AND by this factored form adds a gate. The plane axioms by themselves do not supply that missing fanout condition.

For arbitrary children, removing higher-degree terms preserves which edge pairs a block accepts, but implementing the resulting OR of singleton supports may duplicate shared work. A global charging argument is still required; no unproved claim of cost preservation has been added.

## Boundary certificate route

Drafted results/orch/lemmas/2583_boundary.lean. For an arbitrary bipartite relation I and a monotone candidate F, correctness follows from truth on all incident pair inputs and falsehood on the canonical boundary assignment for every point subset S: points S are true, and precisely the lines nonincident with every point of S are true. A true target input dominates an incident pair; a false target input lies below the canonical boundary for its selected points.

This reduces an order-3 candidate certificate from 2^26 arbitrary assignments to 52 positive pair tests and 2^13 negative boundary tests, plus monotonicity. Source is a draft until Lean checked; no circuit-normalization or size claim is included.

2026-11-25T15:01:43.689556+00:00 Boundary-completeness source checked with Lean (exit 0, no warnings/errors). Validation and SHA256 recorded in results/orch/2583-boundary-validation.txt.

## Stronger local criterion

The local OR-set criterion extends to arbitrary monotone point-only functions A and B. If line l AND A AND B is below incidence, then line l AND A or line l AND B is below incidence. Indeed, evaluate point functions at the largest point assignment disjoint from the neighbors of l. Their AND must be false there, so one is false there; monotonicity then makes that factor false on every point assignment with no neighbor of l. The clean top wire can therefore bypass an immediately preceding point-only AND by rewiring to a child, without new gates. This does not justify changing a shared point-only OR ancestor; that remains the missing global step.

2026-11-25T15:05:37.719975+00:00 Closed-boundary extension checked with Lean, exit 0 and no diagnostics. Source contains 74 new lines above the existing checked base; validation hash in results/orch/2583-closed-boundary-validation.txt.

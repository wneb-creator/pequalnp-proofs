# Algebraic witness strategy

Started around 2026-11-25 03:15 UTC. No counterexample found yet.

## Theta algebra
For three length-three paths between an off-line point x and line y, use point variables a1,a2,a3 and line variables b1,b2,b3. Required terms are x*b_i, y*a_i, a_i*b_i. The only permitted extra minimal terms are a1*a2*a3 and b1*b2*b3. Among all 256assignments, the only free masks in ordering [x,a1,a2,a3,y,b1,b2,b3] are14,15,224,240.

The product (a1 OR b2) AND (a2 OR b3) AND (a3 OR b1) is safe: all of its mixed cubic terms contain a required matching pair, while its two monochromatic terms are allowed triples. However, it misses the required matching pairs themselves, so it is not a witness.

For the full four-path theta, the extra terms are threshold-three terms on the four middle points and four middle lines. No useful factorization found.

## Quadrangle algebra
Label joining lines u=ab,v=ac,w=ad,x=bc,y=bd,z=cd. The product (u OR z) AND (v OR y) AND (w OR x) yields four allowed concurrent stars and four forbidden triangles. Thus the simplest use of the three opposite-line ORs fails exactly on triangles.

## Constructive search
Task scratch algebra_beam.cpp uses canonical free-AND closures on positive signatures. An action joins two positive supports using one OR, while ANDs of all applicable earlier wires are free. It found an eight-OR theta circuit; algebra_verify.py checked all 256assignments against the required interval, with zero errors. Complete recipe: algebra-beam-8b-verified.json. It rejects all four free masks, so this is an alternate baseline, not a counterexample.

The seven-OR beam search was stopped after over20randomized scoring runs, width5000, with no witness. This is only heuristic evidence, never an UNSAT or lower-bound claim.

Quadrangle forced-reuse search fixes the first OR to local inputs4 and6 (global lines0 and2). A thirty-run beam search of total11ORs at width100 found no witness. A stronger search is running with exact set-cover lower bounds and a ten-minute cap.

## Sound search bound
At a negative row j, take the positive signatures of all currently false wires. Let c_j(S) be the minimum number of these signatures covering positive set S. Free ANDs do not improve this cover family. Adding an OR wire of positive signature U that is false at j changes the full-cover minimum to min(c_j(E), 1+c_j(E\U)). One OR lowers it by at most one. Thus c_j(E)-1 is a necessary count of remaining ORs. The search computes these cover numbers by subset dynamic programming (at most12positive edges), using them for pruning and scoring. It still remains a heuristic beam search.

## Independent review
Reviewed parent checkpoint routes-eighteen-exact.lean delta against routes-eighteen-or-gates.lean. Hash1cfafa46de7cb8199c8f49896ce4f68f8669493f283074766cbfefc14868428b matches. Delta adds only a permitted own-namespace18bound lemma applying the prior checked18bound. No51claim or forbidden text. Approved as partial preservation.

## Small core obstruction (computer result only)
For the six-variable core g = a1b1 OR a2b2 OR a3b3 OR a1a2a3 OR b1b2b3, a separate exact Z3 encoding of the canonical free-AND model returned UNSAT for three OR gates in about0.07seconds. The four-OR DNF is immediate. This corroborates a complete small beam frontier (34 first states, then cover pruning), but it is not a Lean proof or an authoritative checker verdict. Saved source: algebra_core3_exact.py; data: core3-truth.json; output: algebra-core3-exact.log in task scratch.

Completed100scoring runs each for the forced-reuse C8 and quadrangle beam searches; no witness. The unconstrained theta4 ten-OR search is running under a ten-minute cap.

## Final algebra status

Completed 2026-11-25T03:38:42.899997+00:00. The unconstrained theta4 ten-OR cover-guided beam completed all100scoring runs (width200) without a witness. All algebra search workers are now stopped. No counterexample, no51bound, and no new Lean file resulted from this route. The independent parent checkpoint review remains approved.
The SAT agent separately confirmed C6 quadratic-only4OR UNSAT, so that small diagnostic is also closed. It reported that another route already found an asymptotic quadratic-shadow counterexample; that result was not independently inspected by this agent.

## Reassigned singleton packing control
At2026-11-25 03:47UTC the parent requested an exact finite capacity-two block-packing control. Both branch-and-bound and unpruned C++ DFS completed exhaustively in about0.05seconds. Maximum removed incidence edges is21, hence31survive. The unpruned search visited189723feasible families, maximum5blocks;936maximizers have3pair blocks on3point/3line coordinates. Independent Python verification checked all468row constraints and52edges for a maximizing example. Complete code/data/logs/hashes are archived in results/orch/algebra-packing. This is a research computation, not a Lean proof.

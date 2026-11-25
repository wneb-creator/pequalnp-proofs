# Structural and AIG route for L-meta-2592

Agent: structural_bound. Started 2026-11-25 14:11:52 UTC. Last update 14:31 UTC.
Root alone holds and renews the lease. This file contains research observations,
not a proof of the posted statement.

## Quantitative obstruction

The checked binary floor is b >= 15. For a live binary/unary DAG with ten
essential inputs, the sum of fanout excess is b - 9. The desired bound is
fanout excess + number of NOT gates >= 11. The existing six distinct branch
wires prove only excess >= 6. In the 19-gate case with four NOT gates, the
floor is tight: b = 15, so all six branch wires have fanout two in a suitable
least circuit. This is the most constrained remaining case, but I have not
proved its exclusion.

## Checked Petersen representation

Take independent set I = {0,2,8,9}. Its complement is {1,3,4,5,6,7}; the
induced edges are exactly (1,6), (3,4), (5,7). Their neighborhoods in I are
respectively {0,2}, {2,8}, {0,9}, {0,8}, {8,9}, {2,9}, all six pairs of I.
The three complement edges pair complementary pairs of I. Thus the function
is the OR of y_ij AND (a_i OR a_j), over all six pairs, and the three products
y_12*y_34, y_13*y_24, y_14*y_23. The standard factored circuit uses 20 binary
gates and no NOT gates. Its fanout excess is 11.

## Cofactor checks and limitations

A finite check showed: after fixing any zero, one, or two input coordinates
without already forcing an edge, every remaining variable stays essential.
There were 1,510 checked instances and no failure. The analogous claim for
three fixed coordinates fails (150 failures among 5,250 instances): fixing
all three neighbors of a vertex to zero deletes that vertex's dependence.
Full results are in structural-cofactor-checks.json in the scratch directory.

This suggests that the first two branch-root signals in a least circuit
must be signed bare inputs, using the fact that a unique path is unate and
cofactor essentiality prevents gating by earlier inputs. This has not been
formalized. Extending it uniformly to three branch roots is unsafe: if two
earlier inputs form an edge, their all-true cofactor already forces the
function, permitting more complicated root signals.

Two active vertices with identical future neighborhoods but distinct past
neighborhoods should not be able to merge into a single Boolean signal:
a past neighbor of one vertex and a common future neighbor expose three
cofactor functions (zero, one, and a variable), which one bit cannot encode.
Triangle/C4 freeness supplies the nonedge needed for that test. This remains
a proof sketch and does not by itself improve the six-branch bound: a
six-vertex cover still gives six singleton active groups. Pairwise separating
assignments for the independent-set/cover partition were checked and saved
in structural-group-separators.json. No valid weighted-fanout inequality
has resulted. No size-preserving NOT-elimination theorem is assumed.

## AIG orientation minimization

Scratch implementation: structural_aig_orient.py. An AIG contains binary AND
nodes with complemented edges, ten input sources, and one free false source.
For each binary node choose whether the physical AND/OR output realizes its
canonical AIG value or its complement. For a source i, charge one shared NOT
if any consumer (including the external output) demands the opposite of the
chosen physical source polarity. Inputs and free false have fixed polarity.
The total is binary-node count plus the number of charged sources. Exhaustive
Gray-code enumeration over all binary-node orientations finds the minimum;
reconstruction shares each complement once and truth-checks the result.
A free-inversion AIG alone is not a counterexample to the posted gate budget.

Own controls passed on 540 random AIGs, 320 random source circuits, 6,772
truth rows, and the known 20-gate Petersen witness (minimum zero NOT gates).
Independent few_not audit passed all 5,110 signed ordered AIGs with zero or
one input and at most two binary nodes: 20,198 orientations and 38,826 truth
rows. Its report is aig-independent-audit.json. This verifies the implementation
on those cases; it is not a formal Lean proof or a synthesis completeness proof.

## AIG SAT/CEGIS preparation

Scratch implementation: structural_aig_sat.py. Binary AND nodes have one-hot
signed-source selectors, sorted within each node. The final node has a free
output complement. Truth rows are evaluated by Boolean CNF; an optional
paid-NOT cap uses the same source-shared orientation cost. The initial rows
are empty, ten singletons, fifteen edge minterms, and fifteen maximal
independent sets (41 rows). Every model is checked against all 1,024 rows.
Counterexamples refine the rows; complete models are orientation-minimized
and reconstructed. All models and full solver stdout/stderr are saved.
A zero-NOT result can acquire a dead NOT when its total remains at most 19.

Short pinned controls passed: 70 random instances testing the true minimum
NOT cap and one lower, plus the known Petersen witness with paid-NOT cap
zero. The decoded witness agrees with all 1,024 rows. Full report:
structural-aig-controls.json. Independent encoder audit passed at 14:31 UTC: 46,588 assignments,
7,254,672 clause evaluations, and 18,116 forward truth-row assignments over
all sorted signed AIGs with zero or one input and one or two binary nodes.
The audit tested every orientation/cap and payment perturbations. Reports
and reproducible audit code are saved in this lemmas directory. No long AIG solver query has started yet; root controls the two
solver CPU slots and renews immediately before launch.


## New active-group singleton strengthening (14:38 UTC)

The original one-bit boundary argument fixes earlier input groups to zero.
Allowing an arbitrary fixed earlier assignment appears to strengthen it:
every boundary group containing any residual-active vertex must contain
exactly that one vertex, with no residual-isolated companion. This is a
semantic proof sketch independently reviewed by proof_strategy, not yet a
Lean theorem.

For vertices u,v in the same proposed group, with u residual-active and
pairwise TwinGroup satisfied, choose a prior vertex a and a future neighbor
w of u so that the restricted graph on {a,u,v,w} has edges av and uw, may
have vw, and has no au, aw, uv. With a=true and other inputs false, the
function on u,v,w is v OR (u AND w). Assigning u,v gives three distinct
functions of w: zero, w, and one. A single boundary bit cannot encode them.
The future w cannot lie in the same TwinGroup because it is adjacent to u.

If v is also active, u and v have the same nonempty residual neighborhood;
C4-freeness makes that neighborhood a singleton w. A prior neighbor of v
cannot be adjacent to u (C4-freeness) or w (triangle-freeness). If v is
isolated, all three neighbors of v are prior. At most one can be adjacent
to u and at most one to w, leaving a suitable a. A finite check of all
1,680 eligible removed-set/pair instances passed; complete witnesses are
saved in structural-singleton-groups.json in scratch.

The existing finite_branch_bit_factor lemma must first be generalized from
prior inputs zero to a fixed arbitrary earlier assignment. Its graph-cut
factorization should then supply the needed one-bit contradiction. If all
six branches are tight, this strengthening would force six singleton cover
vertices and four independent inputs entering only the output read-once
formula. That still does not prove the required weighted fanout bound.

The audited AIG15 query started at 14:32:28.545566 UTC with a 1,200-second
cap and root authorization after a lease renewal at 14:31:26. Full files
are aig15-search* in scratch; exact timings are aig15-timing.json.


## Singleton-support subproblem (14:40 UTC)

For any wire, XOR its Boolean function with its value at the all-zero input.
The normalized singleton-support set is unchanged by NOT. A binary AND/OR
gate gives one of union, intersection, or either ordered set difference,
depending on the two baseline values. Thus arbitrary Boolean circuits induce
a set circuit over these four operations on singleton supports.

The four K4-star OR3 outputs have supports {7,25,42,52} in a six-bit edge
indexing. Any circuit producing all four with at most seven binary gates
has at most three non-goal support additions. A finite search greedily adds
all currently computable goal supports for free, then permits three non-goal
additions. This only enlarges what such circuits can do. The exhaustive
layers had 1,15,189,2060 states and at most 0,1,2,3 goals respectively:
all four were unreachable. Script structural_set_circuit.py and complete
summary structural-set-circuit.json are preserved in the archive.

Few_not independently reviewed the support operation classification and
greedy-closure accounting as sound. Independent re-enumeration is pending.
This is a Python finite check, not a Lean theorem, and it does not finish
the main proof: extracting four exact coefficient guards from the output
read-once formula may duplicate shared AND guards and exceed the available
gate count. That quantitative step is unresolved.

## Final interruption and preservation (14:43 UTC)

Root reported desk HTTP 410 and ordered all new queries/builds stopped.
The AIG15 solver received SIGINT and exited -2. It ran 551.426 seconds,
ending at 2026-11-25T14:41:40.168551+00:00, still on the initial 41-row query
(2,926 variables, 93,487 clauses). No model and no UNSAT verdict were obtained.
Status: INTERRUPTED_LEASE_LOST / UNKNOWN. This is not a proof or refutation.

Full source, dependencies, controls, diagnostics, CNF, manifests, timing,
and research reports are frozen in structural-bound-archive.tar.gz beside
this notes file (244 entries, 823,431 bytes). SHA256:
b1a8ce9fb0bd13fc11243c7838ddc6283a480b7231b5e99bb4f2a89beb98038f.
The archive contains a README explaining reproduction paths and limitations.
Toolchain and few_not were asked to independently check preservation before
root pushes. No child desk request, git mutation, push, or PR was performed.

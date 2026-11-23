# L-lib-123 strategy notes

> Archive note: These are historical research-phase notes. Statements that no repository files were changed describe that phase, before this authorized archival checkpoint. Scratch paths and unpreserved search artifacts below are provenance, not archive dependencies.

The target remains unproved and unrefuted. None of the observations below is a
counterexample to the posted statement.

## Checked baseline facts

`AltLemmas.lean` compiled with pinned Lean 4.36.0 and the pinned project
definitions. The complete log `alt-lemmas-build.log` is empty and the exit
status was zero.

- The three-block predicate expands to genuine existential, universal,
  existential quantification over strings of exactly the prescribed length.
- An alternating predicate independent of the guessed strings is equivalent
  to the original proposition.
- For every `1 <= p < q` and constant `K`, there is an input length `n`
  satisfying `K * 2^(p*n) + K < 2^(q*n)`. The proof explicitly takes
  `n = K + 1`; ordinary constant absorption cannot produce the strict gap.
- Locally satisfiable checks with adaptive final replies do not imply a
  single globally consistent assignment. The checked example is a two-edge
  identity path from false to true: either edge separately has a suitable
  middle value, but no middle value satisfies both edges.

## Full truth-table attempt

A table of all answers on inputs of length `n` has only `2^n` bits, so it
fits the target witness budget when `p >= 1`. The missing operation is a
fast, sound test that this table agrees with the original deterministic
machine. Arbitrary machines need not be self-reducible on shorter inputs.

Recursion on execution states introduces time and cell indices as large as
`q*n` bits. Even for one fixed input, a table of all indexed state bits can
require at least `2^(q*n)` entries. Placing high address bits in the universal
block and giving a local table in the final existential block changes the
dependence structure: the table can adapt to the selected block. The
two-edge example witnesses the logical failure of gluing such answers.

This is not an information-theoretic impossibility result. Actual
deterministic runs on n-bit inputs have at most `2^n` possible values, and
the input itself is a short description of its run. The hard part is fast
opening or verifying that description. General program descriptions do
not come with fast evaluation guarantees.

## Recursive checkpoint attempt

Suppose an interval is partitioned recursively with branch counts
`b_1,...,b_d`. If configurations are fixed before the universal branch
choices, their table must contain every checkpoint in the strategy tree.
The recurrence

    c([]) = 0
    c(b :: bs) = (b-1) + b*c(bs)

has the exact solution `c(bs) + 1 = product(bs)`. Therefore recursive
flattening stores exactly one boundary for each pair of consecutive leaf
intervals, the same number as a direct partition. Nonuniform interval
trees satisfy the corresponding identity
`sum_internal (children(v)-1) = leaf_count-1`.

If every complete configuration has `S` symbols, there are `B` boundaries,
every leaf costs at most `C` steps, and the first witness fits `C`, then

    T <= (B+1)*C,    B*S <= C,
    T*S <= C*(C+S),  and (T <= C or S <= C).

`FlattenBudget.lean` proves the recurrence and budget implications; its
complete build log `flatten-budget-build.log` is empty, with exit zero.
Consequently this particular flattening cannot amplify a logarithmic
space saving into a fixed exponent saving. Putting the checkpoint choices
after all universal choices avoids the table cost but introduces the
unsound adaptive-dependence problem above.

## Graph-interface attempt

If a computation trace could be partitioned into short components with a
polynomially smaller shared interface, the desired quantifier order would
have a natural interpretation: guess interface values, choose a component,
and provide its local trace. The generic multi-stack graph class does not
provide that separator guarantee. I independently inspected the
`prior_routes/four_page_obstruction.md` construction and found no flaw in
its four-page routing or balanced-separator lower-bound argument.

That construction only blocks a method based on page number alone. Even a
fixed machine realizing complicated trace graphs could decide a trivial
language, so graph complexity does not refute the target language-class
inclusion.

## Current unresolved requirement

A successful proof still needs a way to certify arbitrary long
deterministic computations with a polynomially smaller, globally
consistent interface or an altogether different verifier. The tested
obstructions do not prove that no such verifier exists.

## Straight-line grammar commitment attempt

`GrammarBound.lean` compiled successfully with an empty complete build log.
It represents a binary straight-line grammar by topologically ordered
words, each either of length at most one or the concatenation of two
earlier words. For `g` rules and substring length `m >= 2`, every substring
arises either wholly inside a child or across a concatenation boundary.
Descending through children eventually reaches a boundary. There are at
most `g*m` rule/offset pairs, so a generated word containing every binary
word of length `m` requires `2^m <= g*m`.

The same Lean file constructs the explicit recursive enumeration of all
binary words of length `m`, concatenates them, proves its total length is
`N = m*2^m`, proves it contains every such word, and derives the grammar
lower bound. Thus even a short uniform generator can require binary
grammar size at least `N/m^2`, preventing a universal fixed exponent
compression guarantee for this commitment format.

The formal-audit agent independently read the file and found no issue.
The cover deliberately counts some unused boundary cases and arbitrary
terminal pointers, which only weakens the upper bound on its size.

This example does not obstruct richer arithmetic circuits: the bit at
position `j` is selected from the binary representation of `floor(j/m)`
at offset `j mod m`. That direct indexing formula has not been formalized
as a FinTM2 time bound here. It shows why a grammar lower bound must not be
presented as a general summary lower bound or as a refutation of FP3.

## Constructive local stack verifier

`StackTrace.lean` is a complete, checked abstract stack-history theorem,
not just an obstruction. It works for an arbitrary symbol type. Operations
are no-op, push of a symbol, and symbol-checked nonempty pop. It proves
that actual execution from empty is equivalent to indexed height and
matching-push records with the following local tests:

- Push, pop, and no-op obey their exact height recurrence.
- A pop at time `t` points to an earlier matching push `j` with the same
  symbol and pre-push height equal to post-pop height.
- Every intermediate height at `j < k <= t` is strictly larger than that
  matched base height.

Soundness uses persistence of a stack suffix above a fixed depth;
completeness selects the last time at or below the target depth. The file
also proves input-loading prefix equivalence, dependent multi-stack
versions, constant-query pointwise checks, and bounded certificates with
height and matching indices at most elapsed time. The formal-audit agent
independently checked the core proof and found no off-by-one or logical
problem. All current declarations compile cleanly, with an empty complete
`stack-trace-build.log`.

## Eliminating committed matching-push circuits

`StackChallengeExtension.lean` improves the prospective verifier. Its
combined build `StackChallengeFull.lean` compiles cleanly with empty full
log `stack-challenge-build.log` and has also been independently inspected.
The main theorem is exact:

    LegalStackTrace ops T
      iff exists height,
        height(0)=0 and forall t<T, forall j<=T, exists k<=T,
          StackChallenge ops height t j k.

For a pop of symbol `b`, `StackChallenge` requires the correct height
decrement and at least one of:

1. `j >= t`;
2. `height(j)` differs from the target post-pop height;
3. operation `j` is a push of the same symbol `b`;
4. `j < k <= t` and `height(k) <= height(j)`.

The real last earlier visit to target depth cannot satisfy the fourth
alternative, so the universal challenge at that index forces the right
symbol. A false candidate can be answered with a later dip. This removes
the requirement that a short committed circuit compute matching-push
indices. Only operation, height, and machine-control records still need
compact commitments. The final existential block supplies `k` and the
evaluation certificates for the fixed committed circuits.

This is useful proof machinery, but it does not provide the missing
uniform power-saving circuit-size bound for arbitrary deterministic
histories. No claim that L-lib-123 is proved or refuted follows from it.

## Replacing height and control circuits by checkpoints

`CheckpointReplay.lean` proves an exact generic deterministic replay
theorem. A fixed boundary-state table whose adjacent entries agree with
replaying each block must equal the global run at every boundary. Queries
inside a block are then reconstructed from that same table, and all local
validity checks glue to global validity. The endpoint `t = R*B` is included.
The complete compile log is empty; the formal-audit agent independently
reviewed the source and found no indexing or logical problem.

For the prospective stack checker, the replayed state can contain only
finite control and stack-height counters. Separate stack challenge checks
establish the legality of the read symbols. If an operation-history circuit
of size `g` is already committed, the boundary table costs approximately
`T/B`, while reconstruction and circuit certificates cost approximately
`B*g`, up to logarithmic factors. The optimum gives `sqrt(T*g)` rather
than requiring additional height/control circuits. This remains
conditional on a uniform operation-history compression theorem.

## Binding adaptive operation answers by finite batching

The prior-routes agent proved `finite_answer_batch` in
`prior_routes/BatchVerification.lean`; I independently reviewed it. If
every false finite-alphabet answer admits a universally selected refuting
challenge, one universal block can contain such a challenge for every
possible value at every queried index. Consequently, answers supplied in
the final existential block are still forced to be the actual answers.
The encoded application requires a predetermined finite set of indices;
the semantic theorem itself does not impose this resource restriction.

The remaining adaptive dip index in the stack challenge can be eliminated
with fixed block minima. `BlockMinimum.lean` proves minimum existence and
uniqueness, canonical table existence, quotient boundary inequalities,
and an exact interval decomposition. A dip in `(j,t]` is either in one of
the two edge blocks containing `j` and `t`, or in an intervening full block
whose committed minimum is below the threshold. Thus the expensive point
queries are all in blocks chosen before the final existential answers.
Each committed minimum is separately checked by a universal block query.
The full compile log is empty; root independently reviewed the theorem.

With a deterministic point-query generator taking time `T` and space
`T^s` for a fixed `s<1`, ordinary dual checkpointing would give the
finite-alphabet answer verifier cost `T^((1+s)/2)`, and batching with
block minima would yield total exponent `(3+s)/4<1`. No general
point-query generator with that simultaneous time/space bound has been
constructed here. A space-only simulation with uncontrolled running time
does not meet this premise.

## Exact encoding into the posted three-block predicate

`AltEncoding.lean` proves that three equally sized raw bit blocks parse
exactly into an existential/universal/existential relation. Its typed-game
encoding requires a valid first code, treats invalid universal codes as
vacuous, and requires a valid final response code. Given coverage of all
typed values by fixed-length codes, this encoding is equivalent to the
typed game. It also proves that parsing by the actual witness length
divided by three agrees with parsing by the source budget under `Alt 3`.

This last fact supports a total linear-time verifier: malformed short
inputs must not trigger generation of an exponentially large unary source
budget. The verifier can parse its actual input and use an explicit input
length budget. The file establishes semantic equivalence, not decoder or
machine running-time bounds. Its full compile log is empty.

## Independent machine and runtime reviews

I independently read the other agents' circuit-certificate semantics,
actual TM2 radix sorter, actual TM2 adjacent consistency scanner, bounded
global trace game, and normalized original-machine-to-primitive-machine
bridge. No flaw was found in their stated semantic results. The bridge
handles empty pops, pop-and-restore peeks, finite reachable symbol support,
arbitrary initial stacks, absorbed halting, and exact clean output.

These components do not establish a short first commitment for every
source machine. Runtime theorems for structured sorting inputs also need
their explicit malformed-input guards and a linear timeout when assembled
into the posted verifier. None of these auxiliary results is a proof of
the target gap.

## Restricted one-work-tape refinement

The one-work-tape controller protocol received independent matching
resource analyses from the lean-setup agent and me. For spatial width b,
the fixed controller list has about T/b entries. Sort a checked copy by
block and time, then replay one spatial block at a time. The total visit
duration is T; initializing b cells for each visited block also costs at
most about T. The controller list is immutable first-witness input, so
snapshots contain its head index rather than its contents. Mutable replay
space is about b.

Nested deterministic checkpoint verification has cost
`T^(1/3) * b^(2/3)`, in addition to the immutable controller input T/b.
Balancing at `b = T^(2/5)` gives a restricted three-block budget
`T^(3/5)`, up to logarithmic factors. The equivalent sparse local version
stores only internal checkpoints of each block replay; known initial
memory is reconstructed and final local payloads need not be stored.

The root's `ThreeFifthsBudget.lean` proves the matching algebraic budget
relations, which I independently reviewed. This is not a completed
FinTM2 implementation of the restricted simulation. A generic quadratic
multitape-to-one-tape conversion still loses the saving. A hypothetical
T^(3/2) conversion would now suffice, but its proposed remote cache-block
transfer is not implemented: moving b independent symbols across distance
T on one finite-control head is not automatically an O(T) operation.

For the nested complement checker, total time is not the only guard.
Arbitrary first-witness snapshots can become segment starts, so the space
bound must also hold from every decoded snapshot. A fixed-width bounded
configuration encoding with rejecting invalid/overflow transitions gives
this property without altering the genuine replay. Merely knowing a
space bound on the original initial run does not justify all inner
checkpoint sizes.

## Final fresh simulation pass

The child agent `fresh_simulation` independently revisited general
normalization and wrote `fresh-strategy-report.md`. I reviewed its
calculations. The improved restricted exponent leaves a concrete
conditional opening: a cache transfer cost `T*b^rho` with `rho<1/2`
would suffice, with the ideal constant-payload case giving exponent 9/10.
A separate hypothetical compressed-controller representation for a
quadratic simulator would give exponent 4/5. Neither required decoder or
controller representation was constructed.

The report also checks higher-dimensional single-head geometry. The
examined normalization and local-checkpoint exponents compose to a value
strictly above one for every fixed dimension and fixed number of blocks.
These are conditional budget calculations and limitations of the tested
mechanisms, not lower bounds against all possible FP3 proofs. The fresh
pass produced no new Lean theorem or repository mutation.

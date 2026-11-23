# Retained-push generator audit

> Archive note: These are historical research-phase notes. Statements that no repository files were changed describe that phase, before this authorized archival checkpoint. Scratch paths and unpreserved search artifacts below are provenance, not archive dependencies.

The target FP3 theorem remains unproved and unrefuted.

Fix a legal stack run and a final observation time. The pushes whose
symbols remain on the stack at that time occur in chronological order.
Between two consecutive such pushes, the earlier surviving symbol is
never popped. Consequently the deeper retained prefix is inaccessible
and may be omitted when simulating that interval. A simulator only needs
the current retained top symbol and a fresh scratch stack above it.

This is a valid local reduction, but it does not bound the scratch stack.
The interval can be a balanced excursion of height proportional to its
entire duration. Nor does the ordering of retained pushes make the other
stacks independent of that excursion.

A direct embedding shows the issue. Place a tagged sentinel at the base
of one work stack. Simulate an arbitrary source machine above that
sentinel, interpreting a sentinel peek/pop as the original empty-stack
case and restoring the sentinel when necessary. Each source primitive
requires only a constant number of protected-stack primitives. On halt,
retain the Boolean output in finite control, clear the simulated scratch
cells, and push that Boolean above the sentinel. For a source already
using the project's clean-output convention, this cleanup is especially
simple; in general it costs at most linear time in the cells created.

The final surviving push therefore reveals an arbitrary source
computation, even though it is preceded by only one balanced excursion
above the protected base. A fast low-space generator for that emitted
symbol is not obtained from survivor ordering; it would itself be a
general fast low-space simulation theorem. This is a reduction exposing
the premise, not a refutation of its possible truth.

There is a useful restricted case. If each excursion's scratch height is
bounded by b and the other generator stacks are also bounded by b, the
retained prefix can be emitted without being kept in working memory.
Independent finite-state consumers can then be summarized by transition
monoids, as in the prior-routes agent's checked synchronous-consumer
construction. Arbitrary mutable consumers are not covered.

Trying to regenerate discarded deep cells recursively introduces another
dependency: regenerating one stack's old payload may require the other
stacks at that earlier time. All recursive times decrease, so the scheme
terminates, but this alone gives no polynomial-time bound. Branching
recursive reconstructions can unfold a shared dependency DAG into a much
larger tree. Any claimed bound such as T^2/b must explicitly prevent this
repeated expansion; it does not follow from chronological nesting alone.

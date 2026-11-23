# Oblivious dyadic-buffer replay attempt

> Archive note: These are historical research-phase notes. Statements that no repository files were changed describe that phase, before this authorized archival checkpoint. Scratch paths and unpreserved search artifacts below are provenance, not archive dependencies.

This is a prospective universal simulation attempt. It has not supplied a
proof of the posted FP3 statement or a counterexample to it.

The intended reduction stores each simulated tape in buffers of sizes
1, 2, 4, and so on. An oblivious schedule makes the transfer addresses and
times independent of the simulated data. A cache cutoff B retains the
small levels; large-level transfers occur only about T/B times.

The tempting first witness is the list of large-buffer controllers.
Sparse controller events alone are insufficient: each transfer moves B
mutable symbols. Keeping all payloads costs (T/B)*B = T symbols. This is
the same interface volume as direct time-block stack windows.

The next attempt omits payloads and reconstructs a requested one. Once all
write values are fixed, the buffer schedule is only a permutation/copying
network, and its source addresses can be traced cheaply. However, the
write values depend on finite control, which in turn depends on earlier
reads from the other buffers. Predetermined head addresses remove one
source of adaptivity but do not remove this time-ordered dependency chain.
Its depth can still be T.

Replaying a whole source prefix for each large payload gives an apparent
time T*(T/B), but does not itself use only B memory: replaying the prefix
still needs the original mutable tape contents. Thus even the claimed
NTISP(T^2/B,B) bound would require an additional construction. It is not
established merely by writing down this product.

Recursive opening of the buffer payloads has two sound options currently
available: keep all shared payloads fixed before the universal query, or
recompute their common source values. The first returns to linear total
payload volume. The second needs a bounded-time, small-space history
generator, which is the unresolved premise of the earlier positive route.
Letting final existential payloads vary independently by the selected
query is unsound.

A finite transition-monoid summary is a real optimization when a long
produced word is later consumed only by a fixed finite-state machine.
The prior-routes agent formalized such a synchronous producer/consumer
case. It does not extend automatically to arbitrary mutable stack
contexts: two distinct B-bit stacks can be distinguished by a continuation
that pops and checks one of those two words. Consequently a generic exact
online summary supporting every continuation must distinguish all 2^B
stack values. This is a limitation of that summary interface, not of
computation-specific summaries or of short-input languages.

No universal time-space product below T^2 follows from this attempt.

# Global OR-count investigation

`GlobalOrCharge.lean` compiles and extends the circuit part of L599 from active degree exactly two to active degree at least two, without pseudoforest sparsity. If the minimum OR budget violates the conjectural edges-minus-one bound, some active vertex can be deleted with a saving of at least two OR gates. This is an unrestricted monotone-circuit statement.

It does not give the desired 51-OR bound for the plane. L599 uses pseudoforest sparsity precisely to ensure all active degrees equal two after leaf peeling. Its two paid OR gates then match the two deleted edges. In the four-regular plane, deleting the supplied vertex loses four edges while the proof pays only two; the induction no longer closes. The first-OR factor/module argument detects a second release gate, but provides no third or fourth release.

At first inspection, general AND≥13 was not available from vertex cover: L217's arbitrary-circuit cover bound explicitly stops at t≤5, and safe-biclique arguments require an unproved normalization. A newly accepted upstream L1898 subsequently supplied an unrestricted PG(2,3) AND≥13 theorem, now being transferred by line-negation to the posted edge list. If that transfer compiles, OR≥51 would indeed suffice for a full refutation. No such OR bound is claimed here.

Literal 13-AND circuits need not be line-linear: replace one row term p*L by (p OR R)*L while retaining another complete row term R in the final OR. Absorption preserves the exact function and the AND count, although it adds one OR and introduces formal line degree two. The unresolved issue is a size-preserving removal of general absorbed sharing, not this easy redundant example.

Validation: L599 dependency build and GlobalOrCharge.lean each exited 0, complete logs adjacent. Research-only import of L599.

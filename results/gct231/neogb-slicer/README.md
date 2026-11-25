# Untrusted exact-trace dependency slicer

The slicer follows arithmetic and monomial-reference dependencies back from a literal nonzero constant output, retains the original generators, and rejects truncated traces, unsupported late literal-input records, or absence of a constant. It performs no polynomial arithmetic. Its output must still pass the exact polynomial replay.

Independent review PASS is in `review/`, including a fresh row-zero slice and successful unchanged replay proving a nonzero constant. This is a storage transformation, not an additional mathematical theorem.

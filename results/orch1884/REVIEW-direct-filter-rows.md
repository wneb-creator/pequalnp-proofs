# Independent review: DirectFilterRows.lean

UTC: 2026-11-25T16:46:56.330579+00:00

Verdict: PASS for the stated helper scope. Exact source SHA256 `549ffa38c3e0dc9d2571917ad6dbcc0fa33c901ba85b79d9340242f8d752479a`, 2358 bytes/58 lines. Author reported successful Lean exit0; complete named logs were read and hashed, with no error diagnostics and empty stderr. This reviewer did not rebuild.

The finite geometry checks each of the13 negative natural-nine-input rows after inserting originalx0=false. For each row, either inserting filtered vertex1 or5 makes Petersen true, or clearing both filtered vertices leaves a singleton. In the first two cases the explicit factorization contradicts H=true on a negative row. In the last case independence ofH from1and5 transfers H=true to a singleton, contradicting the previously checked singleton rejection. Thus H is false on all13 negative rows under explicit fiber monotonicity, independence and factor assumptions. Independent Python enumeration verified all13 geometry cases. target_rows identifies the full ten-input target on the inserted falsex0 with the displayed nine-input target for every natural mask; positive basis acceptance is kernel checked. The fixed filter pair{1,5} and its coordinate convention are explicit; other pairs need the symmetry wrapper.

Imports are scratch proof dependencies, so this is not a permitted standalone final-import configuration. Correct L_meta_1884 namespace. Any numeric options are scoped over their finite declaration. No forbidden constructs, new axioms, native_decide, unsafe declarations, attributes, strings, or secret-like content; below512KiB. None of these files claims the full posted L-meta-1884 theorem.

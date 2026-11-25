# Exact posted-edge transfer of the accepted AND lower bound

`PlaneAndThirteenTransferSmall.lean` compiled with exit0 under a3GB cap. Its `DifferenceAndLowerBound` hypothesis is exactly the statement of newly accepted upstream L_meta_1898, copied from the refreshed source. The theorem `thirteen_ands` conditionally proves that every Monotone2 circuit for the exact posted52-edge L-meta-650 function has at least13 AND gates.

The transfer fixes point labels and negates line labels modulo13. This converts the posted sum incidence p+l in{0,1,3,9} into upstream difference incidence p=l+{0,1,3,9}. Coordinate edge checks and the52edge range are verified in Lean. The proof maps arbitrary accepted edge inputs and all restricted independent negative inputs, and uses an explicit index bijection to prove relabeling preserves the AND count.

The hypothesis remains explicit in this frozen artifact. The accepted upstream proof has been independently read/matched but has not yet been locally compiled successfully: broad-Mathlib and narrow6GB attempts hit the interpreter memory cap. The complete source plus unconditional adapter is in `PlaneAndThirteen.lean`, still pending validation. No unconditional locally checked13-AND result is claimed from this conditional file alone. Full successful transfer stdout/stderr is preserved adjacent; failure logs remain in the job scratch directory.

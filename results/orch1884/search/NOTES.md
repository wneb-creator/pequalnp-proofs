L-meta-1884 exact synthesis search

The search fixes the mapper to the identity and the free unary function to Boolean negation: wire10 is not x0; gate i outputs wire11+i. It searches the strict earlier-wire AND/OR/NOT subclass, with no constant sources. A returned18-gate witness refutes the posted statement. Solver UNSAT or UNKNOWN is not a Lean proof.

With no paid NOT gates, the circuit is monotone in x1 through x9 for each fixed x0. Exact specification therefore needs only the minimal positive and maximal negative assignments of each cofactor:24 rows at x0=false and14 at x0=true,38 total. All SAT models are independently checked on all1024 inputs. With at most one paid NOT, the seed specification adds low/high-weight assignments and counterexample-guided refinement; full validation remains mandatory.

Validation: known20-gate monotone baseline and a21-gate circuit using NOT(free-negated-x0)=x0 both returned SAT and passed all1024 assignments. The latter is rejected UNSAT with a zero-paid-NOT bound. The encoder allows zero or one paid NOT and does not force any NOT. Source ordering canonicalizes commutative operands; NOT duplicates its selector so it cannot create fake structural uses.

First search:18 gates, zero paidNOT, free negated input required used,38 exactrows; returnedUNKNOWN after119.06 seconds. No target witness. Sourcev1 preserved separately. Added exact-extrema acceleration for a sole paidNOT first on a raw input. The neighbor1 case uses46rows and has a full1024-row pinned validation.

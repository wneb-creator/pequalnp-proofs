# Structural and synthesis work for L-meta-2962

The posted general inequality remains unproved. No strict counterexample has been found. The following results are supporting lemmas and bounded computational evidence, not a completed proof PR.

## Kernel-checked contributions

- `DeletedCover.lean` in scratch, incorporated by the parent: extending a cover of deleted edges by a cover of the residual graph bounds the original minimum cover. A local edge/cover resource certificate suffices for the target inequality.
- `DisjointAssembly.lean`: local certificates combine when the gate cones are pairwise disjoint. This isolates the unresolved sharing cost.
- `AbsorbWrapper.lean`: appending `q = F OR x` and `r = q AND F` preserves the computed function and AO2 well-formedness, gives the exact two new gate values, makes `r` below the graph function and `q` not below it, and makes the accepted-edge set of `r` all graph edges. The original output must name a valid wire. Read-twice and maximal-core results are supplied by the companion agents' separately checked files.
- `MatchingCoverCertificate.lean`: on `Fin (2*m)`, the matching edges `(i,m+i)` force every cover to have at least `m` vertices. A cover with `m` vertices is therefore minimum. The proof avoids exhaustive subset enumeration.

Each standalone file has an empty successful Lean build log and an explicit validation record. Independent review cleared the contributions.

## Computational findings

The Fano single-core search returned UNSAT for all five necessary nine-input support orbits at nine gates, and all fifteen necessary support orbits at ten gates. Additional larger single-core and shared-core searches timed out; those have no UNSAT interpretation. The encoder, symmetry reductions, support projections, and operand-arc budgets were independently reviewed. Several pinned positive controls were checked against every CNF clause, full truth tables, and independent read-vector/core semantics.

A nine-gate single core computing a six-cycle was synthesized and independently checked. With `e = x7*(x0 OR x1) OR x13*(x0 OR x2)`, its output is `(e OR x8) AND (e OR x1 OR x2)`. It has six accepted edges, minimum cover three, one maximal core, and nine gates in that core's cone. Its stronger resource inequality has slack one. Companion work formalized this example in Lean. Eight-gate single-core and seven-gate two-core versions were UNSAT. A nine-gate core with four AND/five OR gates was UNSAT, as was the nine-gate subcase with a non-Below internal AND gate.

The exact theta search with eleven gates, fixed to four AND and seven OR gates, timed out. The highest-priority final searches sought an unrestricted exact 26-gate Fano circuit, one gate smaller than the canonical construction. Such a circuit would yield a strict refutation after three-copy amplification and the checked absorption wrapper. Both persistent retries completed at 07:58:16 UTC with return code 0, giving UNKNOWN after the full 900-second limits. The baseline used 900.068 seconds and the independently reviewed automorphism variant used 900.085 seconds. No 26-gate witness or UNSAT result was obtained. Their original pre-reconnect runs were interrupted, with no verdict; these are recorded separately from completed timeouts.

Authoritative final statuses, parameters, CNF hashes, and completed return codes are in `structural/sat-all-search-summary.json` and each persistent run's `.status.json`. Full stdout and stderr are retained. The final two run stems are `fano-exact-g26-free-resume1` and `fano-exact-g26-orbit-resume1`. The 65 total recorded runs comprise ten SAT cases (nine controls and the non-refuting C6 seed), thirty UNSAT cases, twenty-three completed timeouts, and two interrupted runs. No solver from this work remains active.

# Unresolved step and reusable results

L-meta-1031 asks for a globally minimum binary monotone circuit for every graph with no triangles or four-cycles, with every AND owning a nonempty set of graph edges sharing a vertex. Ownership excludes any edge already made true by an ancestor AND. Semantic soundness of an AND on all Boolean inputs is a different property.

The named file proves the exact requested existential conclusion under the additional premise that a globally minimum normalized circuit exists with exactly one semantically unsound AND. That additional premise has not been derived, and circuits can have multiple interacting unsound ANDs. The unconditional named theorem is absent. The checker rejection is intentional and accurately preserved.

The most direct remaining approach is a global exchange argument controlling the cost of a sound star cover of pivotal edges. FreshBudget supplies a concrete deletion-and-repair inequality, but no universal cover cost has been established. FirstLiteral normalizes an already star-owning first AND while preserving every gate ownership set; it does not establish that the first AND owns a star. The theta and P5 templates give concrete repairs under explicit structural and port-use assumptions, rather than a decomposition of every minimum circuit. FreshBridgeFactors classifies families once their substantial Branch premises are supplied; deriving those premises and handling the rest of the circuit remains open.

Avoid reviving the unconditional OR-count bound OR >= edges - 1: PetersenOrCounterexample is a kernel-checked counterexample with eight ORs for ten edges. Its fourteen total gates do not refute L-meta-1031 because a thirteen-gate star circuit exists. Other component-potential failures are also auxiliary obstructions, not counterexamples to the assigned statement.

Numerical evidence is separate from Lean certification. Both final exact total-gate searches returned UNKNOWN. The P5 frozen-prefix census has no accepted Lean certificate; both retained Lean attempts are labeled UNVERIFIED. Separate alternative lemma files sometimes repeat helper namespaces, so combine selected results deliberately instead of importing every file together.

All checked sources and their build or axiom-audit logs are on pnp/pilot-54. Large native proof traces stayed in scratch; their hashes and reproducible small inputs are retained. No full-proof or reduction PR was opened. The desk initially reported all three reduction slots occupied.

# Independent matching exchange review

Verdict: PASS for partial checkpoint preservation. This review covers the full MatchingExchange.lean, including the constructor wrapper, rather than only the earlier core snapshot.

Reviewed source: results/orch/lemmas/MatchingExchange.lean, 310 lines, SHA256 eede9dcae816833ebc2b948ae5e5fcf455b561d628afed348b0598c7dc288dd4.

The closed exchange compares two circuits of equal gate count. Only gate indices g,h,t change; g and h precede t, their outputs have no readers other than t, and neither is the output wire. The old t is their AND. Their conjunction is explicitly assumed to equal the two-edge matching function on every Boolean input. A prefix induction preserves every other wire, including out-of-range references; the mismatching g,h wires are masked until t restores equality.

The wrapper supplies the actual three gate-list replacements and derives the matching identity from the two explicitly assumed crossed rectangle functions. It proves Monotone2, exact circuitFun equality, equal size, and center-containing pair values at both replacement ANDs, which imply their local star ownership. It does not require private OR support nodes, so those supports may have other readers. It does require closed output wires for the two replaced rectangle gates themselves.

No graph hypothesis, minimum-circuit existence, global HasStarProfile, or general normalization is inferred. All assumptions are visible in the statement. The source uses one allowed Defs import and the permitted auxiliary namespace. No forbidden text, axioms, unsupported decision procedures, strings, or attributes occur; the two local maxHeartbeats options are allowed.

MatchingExchange.validation.txt records exit status 0. The complete matching-exchange-build3.log contains only simp-related linter warnings. This review did not rerun the component build or repository checker. Merge only the full helper body: the earlier Core snapshot uses the same namespace and overlapping declarations.

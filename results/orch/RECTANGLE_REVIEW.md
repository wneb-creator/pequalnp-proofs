# Independent rectangle repair review

Verdict: PASS for partial checkpoint preservation. The global normalization and posted theorem remain unproved.

Review scope is only the new RectangleRepair namespace body, following the separately reviewed ExternalRepair and FourVertexGeometry dependencies. Current body length is 192 lines; body SHA256 is 35a93ee97c9306cb0b1c2f88e7f3547661d9b11685c8a9d8058099bca5fb54d8. The self-contained file has 689 lines, SHA256 cf198bc39c8f9bdaf64f40bb9e0c8b256e4a791cc2affc19835f60cdf48e518e.

The three gate-list replacements preserve length. Their support indices satisfy q<g<h<t and s<h with s distinct from g. Thus both support ORs survive the mutation, and every new wire references an earlier gate or an input. repair_model separately proves IsAO2 preservation when the original circuit is IsAO2. Its two-gate support computations are exact ORs of input variables, with no hidden semantic assumption about unmodified intermediate gates.

two_rectangle_component assumes a Monotone2 circuit computing the exact graph function, the explicit crossed-rectangle gate semantics, two disjoint graph edges, triangle and four-cycle exclusion, the support gate syntax, and the stated index restrictions. It selects one of five finite induced-graph cases, builds the candidate circuit, and proves equal function, equal size, Monotone2, and global BelowF for the two replaced AND gates.

The uniform hreach hypothesis is substantive: for every one of the five candidate circuits and every assignment, truth at the replacement OR gate t implies truth at the circuit output. It is explicitly assumed, not derived from original reachability, graph structure, or minimum size. The main theorem does not itself conclude IsAO2 or HasStarProfile for the full circuit, and does not establish existence of an applicable component in every minimum circuit.

The new body contains no import lines, forbidden text, axioms, unsupported decision procedures, string literals, or attributes. Its helper namespace is permitted and its two local maxHeartbeats options are allowed. Validation records exit 0; rectangle-repair-build2.log contains only a simp warning in a preexisting dependency body. This review did not rerun the build or repository statement checker. Merge only the new body to avoid duplicating dependencies.

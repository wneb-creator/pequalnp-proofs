# Independent review: closed OR and relaxation semantics

Verdict: PASS for both exact auxiliary theorem modules; neither module proves the posted L-meta-1884 statement by itself. Reviewed by circuit_search on 2026-11-25T16:55:38.184753+00:00. No compilation was rerun for this review.

## ClosedRelaxOrGeneral.lean

Reviewed SHA-256 `2ceea11c3fe4341e37b17c882f379e76752c94fdd2741c5801287b3824dc4c7c`, 89 lines, 4,873 bytes. Both operand orders `[t,a]` and `[a,t]` are handled explicitly in the gate-value and factorization steps.

The generic exclusion splits on satisfiability of the partner wire. The satisfiable case uses the existing closed-OR safety theorem; the unsatisfiable case proves that the OR gate copies the earlier wire t, then contradicts global minimum size through no_copy. Thus no unproved partner-satisfiability assumption is introduced. ReadsBack supplies both required earlier-wire bounds.

For the sole-reader application, ReadsBack and prefix_value identify the partner's final value with its prefix value, so the partner-independence argument is not circular. The pre/post avoidance hypotheses and output exclusion are passed to SoleReader.factor. Input t is read correctly through the prefix, and OR commutativity covers the reversed order. partner_safe yields target positivity; hpositive then yields circuit-output positivity needed by the closed-OR exclusion. The singleton assignment provides the final contradiction.

The scope remains explicit: t is 2 or 8; both inputs are distinct; the circuit is monotone, reads backward, and is globally minimum among equivalent monotone circuits; PA/PB/PC, cofactor correctness, positive-row implication, exceptional acceptance, and singleton rejection remain hypotheses. This is not an unconditional exclusion of every OR gate.

## RelaxationSemantics.lean

Reviewed SHA-256 `d5b6b6803ca548fe09855ef6d2c034de6c8db2b600f1a6b5668d4b20dc2afd6c`, 44 lines, 1,722 bytes. The input vector `[4,0,1,6,7,3,5,2,8]` is a permutation. The checked finite identity has the correct composition direction: target(x composed with pins) equals the canonical nine-variable edge function. PermInputs.relabel_size supplies a fan-in-two circuit for that composition with size at most the original; the actual general nine-variable floor gives 16 at most that size, hence at most the original circuit size. No monotonicity premise is needed for this target_floor theorem.

For exceptional_accepted, the explicit equality identifies the exceptional assignment with mask 277. If that row were rejected, StrongRelaxRows.exact_if_exception_rejected plus monotonicity and the 12 positive / 13 negative premises would establish full target correctness. Monotone2 is converted explicitly to FanInTwo, and the 16-gate floor contradicts size at most 13. The accepted branch is immediate. This correctly proves acceptance, not rejection, of row 277; it does not assert that the 25 rows alone determine the target.

## Diagnostics and format scope

I independently found and inspected all four original diagnostic files under `/tmp/oec/pequalnp-pilot-103/`: `1884-closed-general-second.stdout`, `.stderr`, `1884-relax-semantics-second.stdout`, and `.stderr`. All are empty. The zero exit statuses are reported by their author; an empty file alone does not establish an exit code. No new build was run.

The two sources contain no sorry, new axiom, native_decide, string literal, _root_ marker, or non-simp attribute. Their only local option is the permitted maxRecDepth limit in RelaxationSemantics. These are auxiliary modules with scratch imports and namespaces, not standalone single-file PR deliverables; final assembled proof/checker review remains separate.

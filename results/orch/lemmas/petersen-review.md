# L-meta-1884 independent census

The current assignment reports reductions_open=true and reductions_live=3. This does not establish that another reduction is admissible. This reviewer makes no desk calls.

The exact target allows arbitrary relabeling of ten inputs and an arbitrary unary auxiliary function of vertex 0. Every FanInTwo circuit of size at most 18 must disagree with the Petersen edge function somewhere.

## Existing reductions

- R_meta_1884_773 has three hypotheses: input relabeling, normalization of a unary auxiliary input to a free NOT when the output is not the auxiliary wire, and the canonical free-NOT lower bound. The first two are proved exactly by L_meta_2594 (final theorem line 93) and L_meta_2596 (line 528). The canonical lower bound remains open.
- R_meta_1884_1 assumes ordinary Petersen has no circuit of size 18; vertex-deleted Petersen has no circuit of size 15; and two exceptional reader patterns are impossible. Those patterns are input 0 unused with at most two readers of input 10, and a size-18 circuit with a unique OR reader of 0 and a unique AND reader of 10. L_meta_670 (final theorem line 6863) proves the exact vertex-deleted hypothesis. No exact proof of the ordinary or exceptional-reader hypotheses was found.
- R_meta_1884_412 assumes a finite pivotal property and a circuit core involving monotonicity, Petersen symmetry, and three input orbits. L_meta_6081 (line 84) proves the pivotal property. The ledger agent also produced a shorter kernel-checked proof. The core still contains the hard circuit bound.

## Useful completed results

- L_meta_670 proves vertex-deleted Petersen needs at least 16 gates. L_meta_1001 supplies a 16-gate upper bound. The deleted graph lower bound need not be reproved.
- L_meta_5367.R.main (line 7174) converts the older deleted-graph lower bound of 15 into 15 + activeReaders{0,10} <= size for canonical free-NOT Petersen. Its constant-folding compiler removes every active reader of 0 or 10 when x0=false. Replacing its lower-bound parameter with L670 yields 16 + readers <= size, hence at most two such gates in a size-18 circuit.
- L_meta_8131 gives a stronger generic elimination criterion. For a size-at-most-18 circuit, at least three gates reading raw 0/10 or outputs of NOT0/10, AND0, or OR10 imply a size-at-most-15 circuit for the cofactor x0=false, auxiliary=true. With L670 and the cofactor isomorphism, at most two gates lie in this affected set. The exceptional OR0/AND10 pair both become aliases and is not directly excluded.
- L_meta_7314 (line 232) converts canonical free-NOT size-at-most-18 circuits to ordinary size-at-most-18 circuits unless size=18, output=28, and no NOT directly reads auxiliary input 10.
- L_meta_6581 (line 4545) proves ordinary Petersen requires at least 16 AND/OR gates, expressed as countP (fun g => !g.op.eval [false]). Prepending the free NOT to a canonical size-18 circuit gives size 19, hence at most two paid NOT gates. This strengthens the older 15-non-NOT bounds L4725 and L6194.
- L_meta_7493 (line 4117) states a lower bound of 14 non-NOT gates for vertex-deleted Petersen. A stronger consequence is hidden in L670: extract at u=true charges only non-NOT gates, and signedRoot excludes signed Live runs with at most 14 binary gates. The semantic agent extracted a 60-line derivation of at least 15 non-NOT gates, hence at most one NOT in every size-at-most-16 circuit. This derivation passed independent logical review and awaits its build result. L8033, L5094, and L3400 are weaker; L8039 excludes size 15 with two NOTs.
- L_meta_8021 is vacuous: it assumes both no NOT gates and at least one NOT gate. It does not close any Petersen lower bound.

## Complete PR census

A complete gh api --paginate census returned 1133 open PR records. The JSON array and object shape were checked before parsing. No exact 1884 identifier occurred in a title or body; 11884 was excluded as a false positive. Full responses are retained in gap-1884/open-pr-pages.json and its stderr file. Returned URLs use open-goat/pequalnp-proofs; no external writes were performed.

## Latest upstream census

The root fetched a newer upstream snapshot into FETCH_HEAD without changing the worktree. All 150 new Lean sources were read through git show and retained with stderr in gap-1884/new-upstream-review. Their final theorem statements are in new-upstream-final-statements.json. Exactly 140 concern seven-variable finite graphs and ten concern nine-variable graphs. None is a ten-variable Petersen theorem or a reader/NOT-count theorem. L11028 gives a nine-variable lower bound of 16, but L670 already proves our exact required cofactor bound.

## Independent partial reviews

The ledger agent's 35-line petersen-pivotal-checked.lean, SHA bd49351ccb3fce9043abd24f7395206ef59d88df586d769021a56fa94d5b91bf, was approved after its reported successful compilation. The graph and adjacency masks match the target, finite checking uses kernel decide, and the wrapper preserves both pins using their distinctness. This is partial progress, not the full L-meta-1884 theorem.

The CEGIS encoding was inspected independently. Full 1024-input model validation makes a returned SAT witness checkable. Its adjacent-independent-gate ordering restriction is complete by choosing a lexicographically least key sequence over all topological orders: swapping an inverted independent adjacent pair changes neither pair member's parent indices and strictly decreases the first differing key. Later wire renumbering does not affect that comparison. A returned UNSAT result would still need a Lean certificate before it proves the posted theorem.

The 205-line petersen-transitive-checked.lean, SHA 0c361534044d1c14228414935b24297b60b3ca49c98a6a671ddc1e68d43aef8e, passed independent partial review: both funnel exclusions use exact pivotal assignments, moveNine maps are bijective graph automorphisms, and both cofactor interfaces are exact.

The new SAT promise-link tail passed logical review pending its compiled immutable snapshot. It embeds ten-bit rows into eleven-bit rows with bit10 equal to the complement of bit0, and derives lower bounds only under an explicit CNF-unsatisfiability hypothesis. No unsatisfiability is asserted. The root mask-insertion audit checked 23,232 plan pairs on 12 canonical Pv16 formulas, using all 1024 inputs; its negative result applies only to that restricted family.

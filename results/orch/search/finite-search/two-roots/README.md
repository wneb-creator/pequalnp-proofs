# Two dirty rectangles and two clean roots

This is a finite diagnostic of a proposed proof route for L-meta-2602, not a solution or refutation of that posted plane statement.

The encoder chooses a C4-free bipartite graph on 4+4 variables containing the diagonal matching, two dirty rectangles Di=(OR Si) AND (OR Ti) accepting marked pair04, and roots R0=(A OR D1) AND (B OR D2), R1 with each dirty rectangle absent/left/right. It checks distinct-fanin realizability and both formal traces at04. Full graph equality is UNSAT; deleting traces alone or dirtiness alone stays UNSAT. The version on all assignments of weight at most three is also UNSAT. Its 96 KB CNF and 7.3 MB ASCII LRAT certificate are preserved, but the certificate has not been checked by Lean or an independent LRAT checker. This finite shape is far narrower than arbitrary circuits.

The weaker condition output<=G is SAT. The independently decoded example has C8 edges04,05,15,16,26,27,34,37 and:

- D1=(x0 OR x1) AND (x4 OR x5)
- D2=(x4 OR x7) AND (x0 OR x3)
- R0=(x2 OR D1) AND (x6 OR D2)
- R1=(D1 OR D2) AND (x3 OR x5)

Output R0 OR R1 is below G on all256 assignments, accepts matching04/15/26/37, and both traces at04 are false. It uses4 AND and9 OR gates. Its pair shadow is04,05,15,26,34,37; omitted ambient edges16 and27 absorb higher minterms. Thus the proposed two-root clean-fragment shadow-cover-at-most-three lemma is false. The full-function AND-surplus claim remains unrefuted. Agent structure_proof independently audited the encoder and checked all256 semantics/traces for this example. A matching3 full-function instance is a separate SAT positive control, decoded on all256 rows.

Embedding the fragment into the plane using [0,2,4,3,13,25,14,16], plus the nine remaining point stars, yields a58-gate clean partial circuit missing ten edges. The completed width300 beam search through six OR-port injections found no improvement. This heuristic failure is not an impossibility result. The root paused further searches on a desk410 response at04:31 UTC.

All .log files are complete captured stdout/stderr. The two scripts generate and decode CNFs, while c8_extend_virtual.py performs the geometry-compatible prefix-source search. Original scratch paths remain in the scripts. The manifest in the parent directory includes these files. No posted proof has been produced.

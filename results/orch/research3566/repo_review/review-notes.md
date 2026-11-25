# L-meta-3566 independent review

The posted statement has no identified quantifier or constant loophole. `IsAO2`
requires earlier operands and exactly two AND/OR inputs, but leaves the output
index unrestricted. Thus a zero-gate circuit with invalid output computes false.
For stars, cutting the centre fails the extra cover-drop gate bound, but cutting
a leaf works because at least two edges remain in the initial graph. Matching2
and C6 agree with the intended bound. Quantifying z before C is equivalent to
choosing z from an optimal circuit and reusing the residual witness for larger C.

The cover-drop hypothesis is equivalent to tau(cut)+1=tau(G), since adding z to
a cut cover covers G and every G-cover covers the cut. For nonempty cuts the
claim follows from the full m+tau-1 lower bound and the cover-based upper bound.

Exact GitHub search for L-meta-3566 returned zero PRs across all states. The
result was a JSON list below the1000 cap. A broader3566 query was refused by the
installed GraphQL rate guard (exit75); no alternate client or bypass was used.
Local2969/3444/3446 refute specific core-accounting estimates with deliberately
nonminimal circuits. Local4849 has a minimal circuit with a nonedge-accepting AND,
but its graph contains the odd5cycle0-4-7-1-6-0 and is not bipartite. It still has
m+tau-1 gates, so it is not a graph-level counterexample.

`finite_search/synth.py` received independent source review. Onehot selectors,
commutative port ordering, AND/OR constraints, use-all-gates constraints and the
last-output requirement are correct for searching minimal circuits. Boundary
truth-table rows suffice by monotonicity; every SAT witness is additionally
checked on all2^n assignments. UNSAT is diagnostic, not a Lean certificate.

Checked graph-only partial review:
GraphPeel.lean SHA256
6e30a166a6f32fa423692bca6ea4e29e490b1a52c3f595055815470017720c8f
5421bytes,124lines; complete build log clean, kernel78.4ms.
PASS TO PRESERVE. Two distinct edges give a positive-degree vertex leaving an
edge; Mathlib gives exact incidence deletion edge count; Nat.find gives minimum
covers; insertion/erasure of z and the cover-drop iff are correct. Own namespace,
sole Defs import, no prohibited constructs. This is a partial, not the full gap.

Additional preservation reviews, all PASS as partial components:
- Combined GraphPeel+Upper+peel_of_cover_bound, SHA256
  fcf3c0db80231d59fb9dc06951bcde328b0d1889ed591fdae6cb7b93eab5cf76,
  19998bytes467lines. Upper composition preserves earlier wires and exactAO2;
  cover-star decomposition gives size+1<=edges+cover. Conditional peeling proof
  has correct graph-only z choice and handles the bonus via residual mincover.
- Converse, SHA256
  9841665b2baa990911687565525db2e7d9acd3eed7ce81c55a4cd14586a28a96,
  12488bytes258lines. PeelStatement is exactly the desk statement; strong-edge
  induction correctly derives the full bound from it. The open statement is an
  explicit hypothesis, not a claimed proof.
- Restrict, SHA256
  63bee7161700d44108ca262d1938927c77568ee9cbdaa295930f60f6db72e9cc,
  29973bytes677lines. Alias defaults, old/new wire indexing and exactAO2 flags
  are correct. Essential-input restriction with nonconstant residual saves one
  gate; graph specialization supplies both conditions. No errors; harmless
  tactic-linter warnings remain.
- Combined Converse plus not_peeling_of_small_circuit, SHA256
  bc22bca43747625b7a745b1c0bf626beb2b7951d79abe674d7a405973f6e73c0,
  27806bytes619lines. Previous converse unchanged except indentation; a circuit
  beating edges+cover-1 contradicts the derived cover bound exactly. Full named
  build passed14s,5149jobs. The posted theorem remains unproved.

Further library censuses:76files mention junk,64final statements;35files mention
readK/reread,29final statements. There is no general size-preserving normalizer
forcing junk<=1 or readK1. 1501/5779 preserve junk count in TopForm normalization;
4057 and8305 require extra nonedge/unique-owner hypotheses. Among77cover-related
files,43final statements, L_meta_3525 gives the full lower bound for forests
(1730lines/76KB); L_meta_1737 is another forest case. No unrestricted cyclic
bipartite/no-four-cycle result was found.

Read-only public snapshot generated2026-11-25T20:47:08.680Z still marks3566 and
10760 as conjectures(j); neither appears in the graveyard. The59newest feed
records cover20:44:20–20:47:08 and contain no pertinent update. Thus no published
accepted proof explains the old410; the desk's internal cause is unconfirmed.
No desk endpoint or GitHub rate-guard bypass was used.

Narrow counterexample search: mirrored two-channel copies of the11-gate4849
circuit, all2048canonical channel routings, all65536assignments on the16-variable
bipartite double cover: no22-gate solution. Minimum mismatch8844rows. The left
port can be normalized by swapping each output pair, so the routing census is
complete for that paired architecture only. Full data/script are preserved.

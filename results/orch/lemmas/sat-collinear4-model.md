# Noncap four-point witness search

The target is the twelve-edge induced graph on accepted-label points3,4,5,6 and all seven lines. Its eleven inputs are those four points followed by accepted lines7 through13. It differs from the four-cap graph. The three points3,4,6 are collinear; point5 is off that line.

The exact AO encoder searches fifteen binary gates with distinct earlier operands. One of all twelve graph edges is selected by a one-hot vector. Two additional evaluation rows represent its two singleton bases; the opposite base vector seeds each formal derivative. Both output derivatives must be false. Twelve minimal-positive and fifteen maximal-negative rows determine the graph function. No p14, fixed top gate, fixed prefix, or ordinary-minimality constraint is imposed. Supported gates, all-used gates, essential input reads and canonical operand-pair order have the reviewed normalization arguments in status-collinear4-review.md.

The target has2074 variables and37769 clauses. The ordinary fifteen-gate star control is tested with the quiet clauses disabled for all twelve selected flags. Four sixteen-gate quiet controls satisfy the identical quiet model at one extra gate; together their24 quiet flags cover all twelve selectable edges. Complete assignments, all2048 local truth rows, direct derivatives, and full16384-row splices were independently checked.

A local fifteen-gate witness extends to the full Fano function by adding the three omitted point stars (nine gates) and three OR gates. Thus15+9+3=27. The omitted stars have zero derivative in both orientations at any selected local edge, so quiet is preserved. The splice maps accepted line offset l to posted offset -l modulo7. The independently reviewed launch driver checks any actual27-gate candidate again on all16384 truth rows and all21 directed-edge pairs, including both quiet directions at the selected edge.

The immutable target, controls, full review diagnostics and executable audit are preserved here. Active solver logs are excluded until completion. Restoring the bundle and running `python3 status-collinear4-review.py ARTIFACT_DIRECTORY` reproduces the independent audit without a solver.

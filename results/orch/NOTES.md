# L-meta-3443 orchestration

Lease acquired 2026-11-24T17:10:27Z. Parent alone handles desk, git mutations, pushes, and final target file.

Exact statement and desk metadata: /tmp/oec/pequalnp-pilot-35/desk-001.json.

Definitions: lean/PEqualNP/Defs/Core.lean and TopForm.lean. Allowed project imports: PEqualNP.Defs only.

Each agent uses a distinct scratch file in results/orch/lemmas and appends findings here (append only). Never add sorry/axioms or use native_decide. All eventual helpers in target namespace.

Current issue: lake/elan not on PATH; parent resolving environment. Do not install or run cache concurrently.

Direct route: only Defs/Core.lean references maximalCores/IsLiftFixedPoint in current Lean sources; no helper theorem imported by Defs is available. Prepared elementary containment/cardinality partial in results/orch/lemmas/direct.lean, awaiting Lean environment. General antichain connectivity should prove |U0|+mc ≤ gates+1 (empty residual-edge case), but residual-edge charge is the substantive missing argument. Literal independent-token substitution is unsafe for circuits ANDing redundant equal-function cores.

## Independent semantic audit (status_review)

Found a simpler structural counterexample: n=4, star edges 01,02,03. Gates (wire indices) are OR(1,2), OR(4,3), AND(0,5), AND(6,0), AND(7,1), OR(7,8); output 9. Gate 2 computes the star, gate 3 repeats input 0 and is a core, gate 4 intersects with input 1 and is the unique maximal core, gate 5 redundantly joins gate 3 and gate 4. Cores={3,4}; maximal={4}; U0={0,1,2,4}; D={01}; residual edges={02,03}; min cover={0}. All six gates live and lift fixed. Target is 8 <= 7. Independent truth-table/count-vector evaluation confirmed these values and also confirmed the other agent's seven-gate candidate. The defect is that a maximal core can accept fewer edges than an inner core whose output is reused outside its cone; counting only the reused output as boundary does not pay for the inner computation.

Counterexample strategy: random search found 7-gate path counterexample; independently validated parent/reviewer simplification to 4 inputs, 3-edge star, 5 gates [(OR,1,2),(OR,4,3),(AND,0,5),(AND,6,1),(OR,6,7)], output8. Full boolean truth table matches star; joint capped read vectors imply unique core3. U0={0,1,3}; D={01}; rest={02,03}; mincover={0}. LHS7 > RHS6. Exact data /tmp/oec/pequalnp-pilot-35/counterexample/star4.json.

Parent simplified the semantic construction to FIVE gates: OR(1,2), OR(4,3), AND(0,5), AND(6,1), OR(6,7), output8. Independently checked all 16 inputs and proof-tree multiplicity vectors: cores=maximal={3}, U0={0,1,3}, D={01}, residual={02,03}, minimum cover={0}; lhs7 > rhs6. This supersedes my six-gate witness.

Parent: final deliverable is posted exact negated twin L-meta-3444 (file L_meta_3444.lean). Held lease remains original L-meta-3443. Public row original is not open to reductions, so no reduction path. Independent counterexample confirmed n4, five gates, bound 7≤6; cache downloading.

Reduction strategy stopped after concrete counterexample found. Prepared standalone graph/bipartition/C4/minimum-cover finite helpers in results/orch/lemmas/reduction.lean; uncompiled until parent cache completes. Uses same G abbrev as counterexample agent, residual deleted edge D={01}, cover={0}.

Compiled counterexample explanation: A=x0 AND ((x1 OR x2) OR x3), B=A AND x1, output=A OR B=A. The sole maximal core B has U0={0,1,3}; direct-reader exclusion removes A but keeps A's two OR ancestors even though A still needs them outside the core. Thus 3+2+1+1=7 exceeds five gates+1=6. All hypotheses finite-kernel checked by initial full build.

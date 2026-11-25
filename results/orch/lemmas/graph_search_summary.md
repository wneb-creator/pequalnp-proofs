# Independent graph search for L-meta-10760

- Verified a14-gate monotone circuit on all128 inputs in Python; explicit gates/output in graph_search_graph-witness.json. proof_template agent received witness for Lean checking.
- Exhaustive weighted biclique-cover dynamic programming: best formula14 gates.
- MILP allowing shared OR-side computations across biclique terms: objective14 gates. This only describes that circuit class.
- Exhaustive formula DP over8,771 quadratic monotone functions (target-edge subsets plus singleton terms): first target formula at14. This does not prove a lower bound for arbitrary circuits or formulas outside those states.
- Matching upper bounds for all one/two variable zero restrictions are stored in graph_search_restriction-upper-bounds.json. They equal the lower_bound agent table: singleton masks1/2/4/8/16/32→10,64→9; all pair masks→7 except12/68/72→6.
- Stochastic13-gate AND/OR/at mostoneNOT search completed300seconds and1,888,894,440 candidate evaluations. Best candidate disagreed on1 of128 assignments; no counterexample found. Search failure is not a proof.
- Two exact13-gate custom SAT encodings were started (all128 rows; optional canonical topological order). Both were stopped to prioritize the main native/Lean proof route. No SAT/UNSAT conclusion. Encodings were validated by forcing the known14-gate witness; both variants returned SAT.
- Official notes/data/lrat-link/gennot.py enc2 search on21boundary rows,13gates, arbitraryNOT was stopped withoutSAT/UNSAT verdict to prioritize the Lean route and preserve disk. Fullstdout/stderr copied here. Its188,305,408-byte unfinishedLRAT is losslessly preserved in scratch as54,071,135-byte graph-13-official.lrat.gz; archive metadata includes SHA256 verified through decompression.

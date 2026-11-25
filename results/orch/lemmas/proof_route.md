# Structural and repository reuse route

- Checked 997 analogous final one-NOT replacement statements. No seven-vertex graph isomorphic to L-meta-10760 is already proved in those files. Ten have the same degree sequence; detailed results are `/tmp/oec/pequalnp-pilot-178/proof-route-isomorphisms.json`.
- Direct exact edge-list search returned no matching proof.
- Sample-certificate reuse: checked 12 free-negation `inputs : List W` certificate families and 69 `rawP` root-mask certificate families under all 5040 input permutations. None evaluates the target identically on its sampled rows. Minimum distinct assignments were 58 and 37 respectively.
- No vertex-deletion target was isomorphic to any of the 18 explicit six-variable graph final statements found in the repository.
- Structural support bound alone gives six ordinary binary gates, plus one when a NOT occurs. Target appears substantially more expensive, so compact support-only proof templates are insufficient.
- Searching the 75 `sGoal` DAG certificate families for induced five/six-variable restriction bounds; output will be `/tmp/oec/pequalnp-pilot-178/proof-route-restriction-bounds.json`. These can guide certificate_search's lower-bound layering.

Potential structural gate elimination: for an irredundant circuit, first gate joining two inputs with identical sole fanout forces a simple graph decomposition (twins for OR, isolated edge for AND). Our graph has neither. Thus one input may have two consumers, and setting it to false deletes at least two gates. Combining suitable induced-graph lower bounds might prove a strong global bound, but formalizing this is larger than reusing the established certificate machinery.

## Superseded restriction scan — do not use

The first scan incorrectly mapped source helper truth tables using each file’s final theorem graph. Some files copy bounds for an unrelated graph and transfer only a restriction. Consequently the following inferred values are NOT reliable and were retracted to root and certificate_search:

- Delete vertex 0 or 5: at least 10 gates (`L_meta_10620.s49Stock`).
- Delete vertex 2 or 3: at least 10 gates (`L_meta_11425.s46Stock`).
- Delete vertex 6: at least 9 gates (`L_meta_11241.s40Stock`).
- Delete any two vertices: at least 7 gates.
- Delete pairs {2,3}, {2,6}, or {3,6}: at least 8 gates (`L_meta_11381.s36Stock`).
- No six-variable match for deletion 1/4 in those DAG sublemmas; those two restrictions are isomorphic to each other. Their complement is a four-cycle with pendant leaves at adjacent cycle vertices.

All are unrestricted-NOT gate-count bounds. JSON lists source files/lemmas and explicit vertex bijections. These values were sent to certificate_search for its independent validator search.

The full target has independence number 2: its complement is triangle-free. Its false rows are empty support, the seven singleton supports, and the nine nonedge pairs. Complement edges are 01,03,12,16,23,25,34,45,46.

## Correction and verified scan

The explicit six-gate formula `(x0 ∨ x1) ∧ (x4 ∨ x5) ∨ x6 ∧ (x0 ∨ x5)` computes the target with vertices 2 and 3 set false, refuting my inferred lower bound 8. The analogous exceptions are deletion pairs {2,6} and {3,6}. Certificate_search independently obtains double-deletion bounds 7 except these three, which are 6.

A replacement scan derives the restricted function directly from `sBase`, `sGoal`, and the sublemma mask, verifies every sampled assignment and the claimed input bijection, and only then reports matches. Script: `/tmp/oec/pequalnp-pilot-178/proof-route-verified-scan.py`; results: `/tmp/oec/pequalnp-pilot-178/proof-route-verified-restrictions.json`.

The replacement scan checked 584 graph-valued subbounds and rejected 266 non-graph-valued ones. No full target bound was found. Verified DAG subbounds give single deletions 0,2,3,5 at 10 and deletion 6 at 9; pair bounds are 7 except {2,3},{2,6},{3,6}, which are 6.

For the missing single-deletion class, `L_meta_10864.g3` contains `(4,10)` (source vertex 2 fixed false). Decoding its actual `rawP`, `TG`, `NN=438`, and `mz 4` gives 272 sampled rows and all 64 distinct assignments. The target deletion-1 function matches every row under target-to-source map `{0:6, 2:1, 3:3, 4:4, 5:0, 6:5}`; zero mismatches. This directly verifies the semantic reuse, independently of the file final theorem labels.

# Independent review: KWFormula

Verdict: PASS for the positive-formula lower bound. Reviewer circuit_search, 2026-11-25T17:21:50.407553+00:00. Reviewed exact SHA-256 `4a367c8e74da00361e448a190f771d30ac0f4220ebe297bb64cb5339214bfefb`, 161 lines, 8,291 bytes. No Lean build was rerun.

The19 target edges match the posted graph in the same order. The36 negative masks match my independently generated complete maximal-independent-set list exactly; my separate data-generation check covered all16,384 assignments. For this proof the weaker property that those rows are negative is sufficient, and rows_correct establishes exactly that together with positivity of the19 edge rows.

I independently parsed the integer19-by36 weight matrix from the Lean source, checked all dimensions/entries, and verified total weight104. The matrix has31 negative entries, so nonnegativity of individual weights must not be assumed. The cap definition handles this correctly: for every subset of rows incident to a given variable, each permitted column contributes max(0,columnsum). I enumerated every incident-row subset for all14 variables and found cap at most4 in every case; each variable attains4. Exact results are in kw-formula-independent.json.

rectangle_bound first embeds A into the incident rows of the leaf variable. On a permitted negative column, the actual signed columnsum is at most its maximum with0. Extending the resulting nonnegative sum from B to all columns is then sound. This avoids the common invalid step of extending a sum of signed weights directly.

The formula induction preserves exact rectangle partitions. At an AND node all positive rows satisfy both children, and negative columns split into those rejected by the first child and the remainder, which must be rejected by the second. At an OR node all negative columns reject both children, and positive rows split into those accepted by the first and the remainder accepted by the second. split_left/right provide equality of signed rectangle weights on those disjoint partitions. The leaf case requires a positive literal explicitly; a negative literal is not silently treated as a legal leaf. Child leaf counts add, and104<=4*leaves yields at least26 leaves.

This result concerns positive DMFormula14 values, which are trees. It does not imply that an arbitrary Monotone2 circuit needs25 gates: shared subcircuits can unfold into more formula leaves. In particular this module is not a refutation of the posted existence of a24-gate general circuit. A separate no-sharing or controlled-sharing bridge would be needed.

The archived validationJSON matches the source hash and records check_exit0/exportedtrue; both checked stdout/stderr files are empty. Only PEqualNP.Defs is imported. There are no sorry/new-axiom/native_decide/root-marker/string/attribute issues, and only the allowed maxRecDepth/maxHeartbeats limits are set. Final proof-deliverable review remains separate.

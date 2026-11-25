# Lower-bound strategy

Status: direct proof not found. Petersen has 15 edges and vertex cover number 6, hence the known monotone construction uses20 gates. General NOT circuits do not admit that same count without a substantive conversion theorem. Existing R_meta_2592_271 already isolates binaryFloor (15 binary gates) and a 1..4 NOT exclusion.

Partial now being formalized: all ten inputs are essential; output cannot be an input or invalid index; effective fan-in support bound gives size+1≥10+notCount. This yields at most10 NOTs under size19, weaker than desired four but requires no conjectural structure.

Existing reductions: _408 valid-wire/output normalization; _318 cut at last NOT; _271 binaryFloor15 plus fewNot. All3 reduction slots occupied.

## Stronger checked-source adaptation

Upstream L_meta_4725 already proves15+notCount≤size, so the initial support bound is superseded. Upstream L_meta_5236 contains the stronger helper atLeastSixteen for circuits given a free extra OR input. LowerBound16.lean preserves its certificate, changes the namespace, and adds realizePlain using only the ten original pins. The extracted live initial set is then included in the larger permitted input set. It concludes16+notCount≤size for arbitrary circuits computing the full Petersen function, including malformed reads/dead gates. This excludes four or more NOTs in size≤19. Independent review passed; compile pending as of14:22UTC.

Prospective17 route, not yet formalized: the first binary gate combines two primary input signatures. At least one operand must remain available separately because Petersen cannot factor through a two-variable gate while forgetting both operands. After restricting a retained operand to zero, the remaining circuit has a constant live wire and computes a nine-vertex-deleted Petersen function, whose15-binary floor is already certified. The projected_bound contraction charges one extra gate beyond the first gate, giving17 total binary gates. The stronger fact that each operand is retained follows if every two-variable cofactor stays essential in the other variable; then AND/ANDNOT first gates may yield18 because both the retained input and first-gate output become constant. All of this remains unverified. Agent not_elimination owns finite cofactor witnesses and automorphism maps; lower_bound would own the generic tail projection lemma. Work paused pending lease ownership audit.

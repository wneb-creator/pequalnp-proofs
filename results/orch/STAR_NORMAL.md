# Star normalization route

A single-level flattening is not routine for quadratic monotone functions: the general conjecture is false (Jukna, Disproving the Single Level Conjecture, primary paper https://web.vu.lt/mif/s.jukna/ftp/single1.pdf, read 2026-11-25). Those counterexamples use saturated graphs and do not refute our triangle/C4-free case.

Current local exchange: an AND gate can be replaced by a unary OR reading one child whenever that child already implies the complete circuit output. This preserves the function and gate count. A subsequent copy-deletion would strictly shrink the circuit, so minimum circuits cannot contain this pattern. Proof in lemmas/StarNormalForm.lean adapts the proven monotonicity core from L_meta_2772, generalized to replace a complete gate. Compiled successfully with lake env lean, now 456 lines after adding deletion and the strict minimality consequence. Complete latest stdout/stderr is recorded in lemmas/StarNormalForm.validation.txt.

Main unresolved difficulty: a dirty AND gate owning disjoint edges may require multiple downstream filtering AND gates. Replacing it by a child or OR can introduce nonedge outputs. Need global exchange or charging argument; no established normalization yet.

Checked strict consequence: `StarNormal.CopyDeletion.least_no_and_operand_below` excludes any AND operand that already implies the full output in a minimum ReadsBack monotone circuit. It requires no graph restrictions. This rules out some reducible structures but does not handle a genuinely dirty AND whose operands do not imply the output.

Independent review PASS — algebraic_route, 2026-11-25 UTC.

File: formalization-single-reader.lean, 2109 lines.
SHA256: c4a4a5156b8612289115ec2be07491c7d536d464f7533a04892c22ced368780d

Reviewed the new tail from SingleReaderTrace through single_reader_output_derivative, plus the previously reviewed unique-reader graph lemmas. The trace definition uses the actual base-wire Boolean values and the standard AND product-rule/OR sum-rule recurrences. A unique-reader chain dominates the changed input; output false-to-true therefore makes every chain wire change. The alternate operand at each gate cannot be reached from the changed input, so its value remains fixed. At an AND it must be true after insertion and hence already true at the base; this transports a true derivative along the chain. The output corollary is an exact specialization.

The result is generic for the strict DAG model and last-wire output. It does not by itself transfer a circuit through normalization, prove graph-specific equality conditions, or refute the full Fano/cap statement. Those remain separate obligations. Forbidden-token scan on the new tail is clean; the build receipt reports successful compilation.

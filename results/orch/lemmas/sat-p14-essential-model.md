# Compact AND operand incomparability extension

The frozen encoder adds the ordinary27 minimality consequence that each active AND atom has incomparable operand functions on the37 maximal-negative Fano assignments. For each direction, a Boolean variable records first-operand true and second-operand false on each negative row. The active atom must have a witness in both directions.

If operandA implies operandB on every maximal negative, replacing AND(A,B) byA preserves every negative boundary output and can only increase positive outputs. Propagating aliases and function-only idempotence gives an ordinary Fano circuit with at most26 gates, contradicting the accepted27 lower bound. This argument need not preserve derivatives. It applies to the exact27 reconstructed circuit; it is not a claim about arbitrary larger circuits.

The extension adds1332 variables and4032 clauses at cap18, for32615 variables and137411 clauses total. All earlier quiet, topological, nine-free, and host constraints remain byte-for-byte in the prefix. Inactive atoms are explicitly exempt from the witness requirement.

The canonical exact28 quiet Fano control passes the new cut with equality/nine-free restrictions disabled. It has7 AND atoms under cap8, so also checks an inactive suffix. The hosted matching control validates the prior equality/nine-free model with this Fano-minimality cut disabled. Neither control is an exact27 Fano witness. Independent constructive review reconstructs every new target clause, checks complete controls and all16384 truth rows, both raw marked derivatives, the negative-row census, and the primitive truth table.

No solver has run on this variant yet. The current nine-free worker remains unchanged. Restore the manifest files and run `python3 constructive-essential-audit.py ARTIFACT_DIRECTORY` for the independent audit. Encoder execution additionally requires the frozen compact, quiet, and nine encoders referenced by the prior manifests; the solver binary is not archived here.

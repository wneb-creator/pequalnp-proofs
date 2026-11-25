# Independent review: SoleReaderFactor

UTC: 2026-11-25T16:41:59.665660+00:00

Verdict: PASS. Exact source SHA256 `ba81489ac7f10173082d77106c728eaf0e1d9964249de13067e48c6e75a03357`, 5415 bytes/118 lines. Author reported Lean exit0; the complete second-run stdout has only unused-simp warnings and stderr is empty. This reviewer did not rebuild.

`agree` compares equal-length banks outside a specified existing input position. Its length bound prevents an appended gate wire from coinciding with that exceptional position. `gate_agree` uses the explicit absence of that input from a gate; consequently `run_agree` applies to arbitrary gate operations, including NOT. `partner_independent` compares the selected prefix-bank wire at any index different fromt; invalid indices have the same false default. It deliberately proves a prefix-bank statement, so a use with a full-circuit partner also needs the earlier-wire persistence/backward-reference bridge.

`factor` splits the actual circuit into prefix, sole reader, and suffix. Both surrounding lists explicitly omit rawt. Equality of the selected reader outputs extends the bank agreement, and suffix evaluation preserves it; output≠t yields the result. `ofFn_agree` handles both valid Fin coordinates and false default indices. `factor_or` and `factor_and` specialize the reader to the two displayed inputs and use persistence of the raw input across the prefix. No monotonicity, gate count, backward-reference, or partner-independence hypothesis is silently assumed by these exact factorization statements; the caller supplies reader-output equality.

The file imports only PEqualNP.Defs, uses namespace L_meta_1884.SoleReader, and has no options, attributes, strings, forbidden constructs, new axioms, unsafe declarations, or secret-like content. It is below512KiB. It does not itself extract a sole reader from a circuit or prove the target exclusion.

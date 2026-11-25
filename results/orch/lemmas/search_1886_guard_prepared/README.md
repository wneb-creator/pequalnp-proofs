# Prepared AND-bank source-guard search

This is prepared search code, not a completed long search or a Lean result. The L-meta-1886 lease was withdrawn before a long run could be started. No valid counterexample or UNSAT result is claimed.

The variant supplies AND(0,1), allows18 counted gates and at most one NOT, and optionally warms from the canonical18-gate overapproximation. Once all30 critical rows exist, each NOT gate is constrained so that its selected source is true at some maximal-zero row and false at some edge row. These restrictions are intended to instantiate the root agent's AND-bank source-incomparability lemmas under their circuit-size, monotonicity and live-consumer assumptions; this archive validates the encoding, not a new proof of those mathematical lemmas. The optional forced-NOT flag adds a NOT-presence clause only after the zero-NOT warm control, thereby excluding the monotone search branch.

The one-second Petersen control reproduced the near-circuit, independently found its four known errors, added them and the guard restrictions, then returned UNKNOWN. That control preceded an incremental API hygiene fix: the final source now freezes every stored per-row source-value variable before any solve, because guard clauses may refer to it after an earlier solve. The final source was statically reviewed, and a separate tiny API regression checked this frozen-row reuse. No Petersen search was rerun after the lease withdrawal.

The final independent review report records the source hash,122 finite source checks, conditional scope, the pre-fix control, and the frozen-row API regression. Build the v2 wrapper as documented in sibling `search_1886_broad`. The prepared command, not a completed long run, is:

```sh
python3 /tmp/oec/pequalnp-pilot-92/search-1886-cegis-andguard.py --edge-op and --gates 18 --min-not 0 --max-not 1 --seconds 600 --warmfile /tmp/oec/pequalnp-pilot-92/local1886-near-canonical.json --force-not-after-warm --output-prefix /tmp/oec/pequalnp-pilot-92/search-1886-andguard18
```

This archive is frozen. All data is public circuit/search material; no environment values or credentials were read or saved.

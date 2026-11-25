# Further L-meta-1886 search results

No valid counterexample or UNSAT result was found. This frozen archive contains three completed 600-second searches and a one-second warm-start control. All long-run stdout and stderr logs are preserved.

The broad search allows 18 sequential AND/OR/NOT gates over identity inputs and free OR(0,1), with zero to two NOTs. It uses effective-parent gate ordering and output-cone liveness, with earlier-wire sources. CaDiCaL retains learned clauses while the encoder adds truth-table counterexamples. It first found a model for 30 rows after 24.6 seconds. Full validation rejected that model on 870 of 1024 rows. The search added 64 failures and timed out UNKNOWN on the resulting 94-row instance after 600.002 seconds. The rejected model, complete final DIMACS CNF, and metadata are included; the candidate is explicitly marked nonqualifying.

```sh
python3 /tmp/oec/pequalnp-pilot-92/search-1886-cegis.py --edge-op or --gates 18 --min-not 0 --max-not 2 --seconds 600 --output-prefix /tmp/oec/pequalnp-pilot-92/search-1886-cegis-or18 > /tmp/oec/pequalnp-pilot-92/search-1886-cegis-or18.log 2>&1
```

The other two completed searches also ended UNKNOWN: free AND(0,1), followed by 17 monotone gates and a final OR with the free edge; and free OR(0,1), followed by 18 monotone gates. Both enabled reviewed ordering and liveness. Their source and controls are in the sibling `search_1886_initial` archive.

```sh
python3 /tmp/oec/pequalnp-pilot-92/search-1886-firstnot.py --edge-op and --not-input -1 --gates 17 --final-or-edge --ordered --live --output /tmp/oec/pequalnp-pilot-92/search-1886-and-finalor-ordered.cnf
/tmp/oec/pequalnp-pilot-92/lean-4.36.0-linux/bin/cadical -t 600 -w /tmp/oec/pequalnp-pilot-92/search-1886-and-finalor-ordered.sol /tmp/oec/pequalnp-pilot-92/search-1886-and-finalor-ordered.cnf > /tmp/oec/pequalnp-pilot-92/search-1886-and-finalor-ordered.log 2>&1
python3 /tmp/oec/pequalnp-pilot-92/search-1886-firstnot.py --edge-op or --not-input -1 --gates 18 --ordered --live --output /tmp/oec/pequalnp-pilot-92/search-1886-or-monotone-ordered.cnf
/tmp/oec/pequalnp-pilot-92/lean-4.36.0-linux/bin/cadical -t 600 -w /tmp/oec/pequalnp-pilot-92/search-1886-or-monotone-ordered.sol /tmp/oec/pequalnp-pilot-92/search-1886-or-monotone-ordered.cnf > /tmp/oec/pequalnp-pilot-92/search-1886-or-monotone-ordered.log 2>&1
```

## Prepared warm start

The separate warm encoder gives the known 18-gate overapproximation as temporary assumptions, initially omitting its four incorrect maximal-independent rows (69,104,521,548). The one-second control reproduced that circuit, independently confirmed its four errors, added those rows, cleared the assumptions, and continued on all 30 critical rows plus the all-zero and all-one inputs. It then timed out UNKNOWN. A tiny independent API control verifies that assumptions clear between solves. These controls do not constitute a lower bound or a counterexample.

```sh
python3 /tmp/oec/pequalnp-pilot-92/search-1886-cegis-warm.py --edge-op or --gates 18 --min-not 0 --max-not 2 --seconds 1 --warmfile /tmp/oec/pequalnp-pilot-92/local1886-near-canonical.json --output-prefix /tmp/oec/pequalnp-pilot-92/search-1886-warm-control > /tmp/oec/pequalnp-pilot-92/search-1886-warm-control.log 2>&1
```

Build the v2 shared wrapper as in the sibling initial archive, replacing `search-cadical-wrapper.cpp` with `search-cadical-wrapper-v2.cpp` and output `search-libcadical.so` with `search-libcadical-v2.so`. The original shared library was not overwritten while a solver used it. Independent review reports are included. No long warm-start search result is included in this folder. Nothing here is a Lean proof or certificate.

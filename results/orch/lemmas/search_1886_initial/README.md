# Initial L-meta-1886 search archive

No counterexample or UNSAT result is claimed here. The two completed searches in this folder each reached a 600-second limit and returned `c UNKNOWN`. Their full stdout and stderr logs are included. Both use identity input mapping and a free edge OR(0,1): one fixes a counted first NOT of input 0 followed by 17 AND/OR gates; the other permits 18 AND/OR gates.

The first template has 38 exact cofactor-critical rows; the monotone template has 30 (15 minimal true edges, 15 maximal independent sets). The decoder validates any SAT candidate on all 1024 inputs. Positive controls in this archive are deliberately oversized and are not counterexamples.

## Commands for completed searches

Restore scripts and data under `/tmp/oec/pequalnp-pilot-92/` before reproducing. The executable is the CaDiCaL bundled with the installed Lean distribution.

```sh
python3 /tmp/oec/pequalnp-pilot-92/search-1886-firstnot.py --edge-op or --not-input 0 --output /tmp/oec/pequalnp-pilot-92/search-1886-or-not0.cnf
/tmp/oec/pequalnp-pilot-92/lean-4.36.0-linux/bin/cadical -t 600 -w /tmp/oec/pequalnp-pilot-92/search-1886-or-not0.sol /tmp/oec/pequalnp-pilot-92/search-1886-or-not0.cnf > /tmp/oec/pequalnp-pilot-92/search-1886-or-not0.log 2>&1
python3 /tmp/oec/pequalnp-pilot-92/search-1886-firstnot.py --edge-op or --not-input -1 --gates 18 --output /tmp/oec/pequalnp-pilot-92/search-1886-or-monotone.cnf
/tmp/oec/pequalnp-pilot-92/lean-4.36.0-linux/bin/cadical -t 600 -w /tmp/oec/pequalnp-pilot-92/search-1886-or-monotone.sol /tmp/oec/pequalnp-pilot-92/search-1886-or-monotone.cnf > /tmp/oec/pequalnp-pilot-92/search-1886-or-monotone.log 2>&1
```

## Prepared stronger encoders

The source also includes optional ordered gates and output-cone liveness. Greedily choosing the smallest ready gate orders by (largest parent, smallest parent, operation): a newly ready gate uses the newest output and thus has a larger maximum parent. Unused gates can be removed and identity gates appended. The separate fixed-guard encoder supplies one binary guard and its NOT, then 16 monotone gates. These options received independent review; the reports and small exhaustive checks are included.

The CEGIS encoder supports all three gate types, a NOT-count bound, effective maximum-parent ordering, and persistent learned clauses while adding violating truth-table rows. Its fixed 22-gate control (the known 20-gate monotone circuit followed by two cancelling NOTs) returned SAT and independently matched all 1024 inputs. This folder contains no long CEGIS search result. `min-not=0` is the complete output-cone mode; a positive lower bound on NOT count alone can omit circuits whose only NOT gates are unused.

The C wrapper uses the existing installed `libcadical.a`; no solver was downloaded. Build it with:

```sh
g++ -shared -fPIC -o /tmp/oec/pequalnp-pilot-92/search-libcadical.so /tmp/oec/pequalnp-pilot-92/search-cadical-wrapper.cpp /tmp/oec/pequalnp-pilot-92/lean-4.36.0-linux/lib/lean/libcadical.a /tmp/oec/pequalnp-pilot-92/lean-4.36.0-linux/lib/libc++.so.1.0 /tmp/oec/pequalnp-pilot-92/lean-4.36.0-linux/lib/libc++abi.so.1.0 -Wl,-rpath,/tmp/oec/pequalnp-pilot-92/lean-4.36.0-linux/lib
python3 /tmp/oec/pequalnp-pilot-92/search-1886-cegis.py --edge-op or --gates 22 --min-not 2 --max-not 2 --seconds 10 --seedfile /tmp/oec/pequalnp-pilot-92/search-1886-cegis-control-seed.json --output-prefix /tmp/oec/pequalnp-pilot-92/search-1886-cegis-control
```

The [official C header](https://github.com/arminbiere/cadical/blob/master/src/ccadical.h), read 2026-11-25, describes the interface as a “C wrapper for CaDiCaL's C++ API following IPASIR.” Runtime signature was `cadical-2.1.2`. Tiny incremental SAT-to-UNSAT and timed termination controls passed. No environment values or credentials were read or saved.

All results here are computational controls or UNKNOWN searches, not Lean proofs or certificates. This archive is frozen.

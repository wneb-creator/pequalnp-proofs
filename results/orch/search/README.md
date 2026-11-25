Search checkpoint for L-meta-2592

These are computational search programs and reference data, not Lean proofs. No search result establishes the posted universal theorem.

The exact source copies are hashed in SHA256SUMS. Programs use Python3, the installed system libz3.so.4 through ctypes, and (for the initial stochastic run) a C++17 compiler. They use no network and no credentials.

search.py searches the 10-input Petersen edge function. cofactor.py searches the 9-input function obtained by fixing original vertex0 false and renumbering original vertices1 through9 as0 through8. Gate data uses operation0=AND,1=OR,2=NOT,3=constanttrue. Inputs are numbered0 throughn-1; source n is constantfalse; gate i produces source n+1+i. NOT ignores its second source.

Reference21 is a known20-gate monotone circuit plus one unusedNOT. Cofactorreference17 is a known16-gate monotone circuit plus one unusedNOT. These references validate the encoder and exhaustive truth-table evaluation. They are not counterexamples to any19-gate or16-gate claim.

The original scratch root used by these exact programs is /tmp/oec/pequalnp-pilot-103/counterexample/. For reproducibility, place the files there or edit the scratch-root path, recording the new hashes. For example:

    python3 search.py --case any --ordered --max-nots 2 --eager-sat --timeout-ms 300000
    python3 cofactor.py --case any --ordered --not-count 1 --eager-sat --timeout-ms 300000

The optional distinct-function restriction compares functions only on initial examples; it is intended only to find witnesses. An UNSAT result with that restriction is not a full search result. The default all-gates-used restriction is also recorded explicitly. All found candidate circuits are independently evaluated over every input in the script before WITNESS is printed.

neighborhoods.py fixes all but each chosen triple of gates in near19.json. Its UNSAT results establish only those finite neighborhoods. The broad global searches so far timed out or were interrupted without a verdict.

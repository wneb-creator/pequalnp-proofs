These files preserve bounded circuit-synthesis attempts for L-meta-2592. No witness or lower-bound certificate was found. SAT UNKNOWN outcomes are not proofs.

The graph has edges 01,12,23,34,40,05,16,27,38,49,57,79,96,68,85. The known candidate has 18 effective monotone gates and four false-positive inputs.

Signed route: gen-signed.py produces the normalized18-binary full-row CNF; add-signed-cost.py imposes a shared-wire complementation budget for actual total size19. phase-signed.cpp uses the CaDiCaL C++ API; decode-signed.py reconstructs an actual AND/OR/NOT circuit and checks all1024 assignments. The scripts use scratch paths and must be adapted to a new checkout.

Monotone route: repository notes/data/lrat-link/genmono.py with arguments 10 18 and the above edges and rows,lex produces a30-row CNF. The15 minimal true rows and15 maximal false rows determine any monotone circuit on all1024 assignments. phase-mono.cpp seeds CaDiCaL from signed18-seed.txt. decode-mono.py reconstructs18 AND/OR gates, adds one unused NOT, and independently checks all1024 assignments. mono18-validation.json records boundary completeness and the canonical seed's exactly four failed clauses.

Large CNFs, binaries, and live solver output were deliberately excluded. Root owns the Lean partials and all submission actions.

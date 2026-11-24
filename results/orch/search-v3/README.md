# Counterexample search snapshot v3

No smaller circuit witness has been found. The saved solver logs are complete. They are computational diagnostics, not Lean proofs.

Search.py is general backward binary AND/OR synthesis on positive edge pairs and maximal negative assignments. It requires every gate to be used, every gate to fire on a positive pair and fail on a negative, and by default incomparable operands. Exact-size UNSAT under these constraints alone does not establish that every smaller size is impossible. --no-incomparability permits absorption padding. --dirty requires at least one AND to fire on a negative assignment. --first-pair-orbits validates every supplied permutation against all edges and checks that its representative images partition all first-input pairs.

SearchFactored.py compresses OR trees into source sets. AND operand sources may be primary inputs, optional shared linear OR forms, or preceding ANDs. The OR output selects AND nodes. Ordinary operand OR trees are not shared. --junk-count restricts the first J hidden ANDs to fire on some negative, omits them from output, and requires all later clean ANDs in output. Clean ANDs may read only primary inputs, shared linear OR forms and the hidden ANDs. It imposes a safe lexical order on independent clean tops. This is a restricted model, not a complete circuit normal form. The source-set selection budget exactly equals binary gate cost after expansion. SearchDecode.py checks decoded witnesses against every edge-positive and every left-subset negative.

Completed runs:
- General K6-incidence binary size34: 1800-second cap, no verdict. Full search-k6-34.log.
- One dirty hidden AND plus6 clean tops, size<=34, no shared linear OR: UNSAT in1.27s. Full search-one-junk-size34.log.
- Two dirty hidden ANDs plus5 clean tops, size<=34, no shared linear OR: UNSAT in21.98s. Full search-two-junk-and7-size34.log.
- Two dirty hidden ANDs plus6 clean tops, size<=34, no shared linear OR: 180-second cap, no verdict. Full search-two-junk-and8-size34.log.

Calibration: SearchCalibrate.py assigns a known dirty C6 size10 circuit and verifies every one of8361 generated clauses. It also canonicalizes a known alternative6 core size29 circuit under all24 automorphisms and verifies all510628 generated clauses. Full search-v3-calibration.log. The saved36/40-gate factored calibration witnesses are correct but exceed the target.

Reproduction examples, run from repository root (place output under task scratch):
```
python3 results/orch/search-v3/Search.py --case c6 --gates 8 --dirty --output /tmp/oec/pequalnp-pilot-29/search-c6-dirty8.cnf
python3 results/orch/search-v3/Search.py --case plane_local --points '0,1,2,3,8,15' --gates 28 --no-incomparability --first-pair-orbits results/orch/search-v3/alternative6-automorphisms.json --output /tmp/oec/pequalnp-pilot-29/search-alternative6-sym28.cnf
python3 results/orch/search-v3/SearchFactored.py --ands 7 --size 34 --junk-count 2 --output /tmp/oec/pequalnp-pilot-29/reproduce-two-junk-and7.cnf
```

The first two example searches were queued at snapshot time. Alternative6 unsymmetrized size28 SAT and global-plane stochastic run002 were still running. No timed-out or running search is labeled UNSAT.

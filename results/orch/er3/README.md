ER3 factoring and bounded searches for pilot 31

These files preserve computational evidence and reproducible programs. They do not prove L-meta-2028 or its negation.

Completed:
- Seven-AND unrestricted-OR synthesis: UNKNOWN after 600 seconds.
- Shared A preprocessing with five gates, six gates per local piece, seven final gates (30 total): UNSAT in 2.25 CPU seconds. This excludes only that decomposition.
- The 31-gate shared-A positive control was SAT and verified on all 8192 inputs.
- The safe-OR positive control uses 32 gates for the ER3 function and OR(11,7). Adding the center/private-leaf gadget gives 35 gates on a 15-vertex graph with 27 edges and cover number 9, meeting bound 35. Verified on all 32768 inputs.
- No useful safe-OR wire or single-gate semantic rewrite in either exact 31-gate circuit or the exact 30-gate circuit for ER3 with edge {5,6} removed.
- No gate-deletion plus one-gate replacement improvement of the algebraic 31-gate circuit.
- No proper C4-free quotient among 12603 loopless input partitions with at most three identifications.

Prepared but not run at preservation time:
- `er3_shared_aux.py --shared 5` searches for ER3 plus a safe-OR output in 31 gates. Such a result would produce a 34-gate extension beating bound 35. Its encoder and decoder passed independent review; only its 32-gate control has been run.

Inputs are polarity3.json and near-polarity3.json. CNF files are reproducible from the encoders and were omitted from this archive. Use a fresh output stem: encoders write metadata to the matching `.json` path. Complete stdout/stderr logs for completed searches are included.

The shared encoders import the adjacent synth.py CNF helper; the historical scratch path inserted by them is harmless when absent because Python also searches the script directory. The C++ rewrite program takes er3-rewrite-input.txt. Generated controls and models include explicit gates and output wire indices. Solver models are validated by the corresponding decoder, including complete truth tables, C4-freeness and exact minimum cover.

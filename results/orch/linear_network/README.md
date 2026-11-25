# Restricted network searches for L-meta-9811

These artifacts are computational evidence only. They do not prove the posted arbitrary-circuit lower bound in Lean.

`enumerate.cpp` is self-contained C++17. Compile with `c++ -O3 -std=c++17 enumerate.cpp -o enumerate`, then run `./enumerate 300`. Its completed log is `enumerate-constants.log`; validation and coverage details are in `validation.txt`. The seven-input neighborhood family is encoded directly. No network with at most eleven gates was found after exhaustive enumeration of at most four non-target auxiliary functions.

The other Python scripts and logs record restricted SAT repair attempts. The scripts retain their original scratch paths; `synthesize.py` and both seed circuits are included to preserve the encoder and inputs. Full generated CNFs remain in scratch, with their SHA256 hashes in `artifact-manifest.json`. Solver logs are complete under `solver-logs/`.

A solver timeout means UNKNOWN. UNSAT here refers only to the displayed fixed-topology or selected-gate models, not to all circuits.

# Search artifacts for L-meta-2732

These are research artifacts, not an accepted proof or an exhaustive negative result.

The original working directories were under /tmp/oec/pequalnp-pilot-70/. Some scripts retain those paths. The per-strategy notes in ../lemmas/ record commands and solver provenance. Generated CNFs can be recreated from the saved sources; the third-party solver checkout is not copied here.

The completed stochastic and bounded subgraph logs are saved in full. Active solver logs will be saved when their runs finish. Source hashes and the snapshot time are in manifest.json.

Known result: the saved 27-gate baseline has been independently checked on all 16,384 inputs and in Lean. No 26-gate witness or general lower bound has been established.

The four bounded subgraph inputs and their complete UNKNOWN solver logs are included. general-reproduction.json records the flags needed to reproduce the initial general CNF exactly.

The 07:32 UTC snapshot preserves completed and interrupted searches separately. Both third-prefix CaDiCaL and AND-root Kissat processes were lost during the environment restart; their partial logs establish no SAT or UNSAT verdict. The new focused F0+A search was running and its live logs are excluded. Source-only and experimental artifacts are not Lean certificates.

The08:00 checkpoint adds the direct24+2 cofactor route, exact bounded-edit neighborhoods, and correlated-cut families. Four completed k2/k3 neighborhood searches are UNSAT only within their stated neighborhoods. Two45-minute searches were active, and their live logs are deliberately excluded. Earlier F0 helper revisions used a three-gate extension; the current helper retains that behavior through --method shannon, while direct is the corrected default. Historical exact source hashes remain in earlier checkpoint commits. None of these artifacts proves or refutes the posted unrestricted statement.

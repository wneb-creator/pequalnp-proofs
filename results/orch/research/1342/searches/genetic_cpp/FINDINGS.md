# L-meta-1342 bounded genetic search

No valid 21-gate witness was found. All best candidates remain invalid. No heuristic run is an exhaustive result.

The graph has11 inputs and16 edges. Fitness initially uses every edge pair plus every maximal independent set (40 rows total). Since candidates contain only monotone AND/OR gates, agreement on these rows suffices for the output function; every zero-fitness candidate is additionally required to pass all2048 assignments and legal wiring. No zero-fitness candidate occurred.

Search evolved through canonical22→21 deletions, original/corrected L1006 seeds, two triangle-CNF24→21 seeds, the five verified neutral-unit22 seeds, and the verified two-junk22 seed. Later versions reject equal operands, penalize any gate column equal to an earlier wire on the40 boundary rows, and archive two-junk near candidates only with both junk AND gates active and no duplicate columns. Enriched runs retain all40 boundary rows and add24 positive assignments containing exactly one graph edge. The final balanced engine keeps exactly7AND/14OR gates and adds function-preserving associative rotations.

Raw early two-junk counts include redundant/dead gates. Only irredundant snapshots from run-41342 onward should be used as substantive near architectures. Independent fulltruth audits of run-51342 snapshots are in prefix-near-audit.json.

Best fulltruth near candidate: run-81342.json.row-39.json. Its output is F OR(x9 AND x10), with exactly four false positives1536,1538,1544,1546 and no false negatives over2048 inputs. It has21 active gates,7AND/14OR, two genuine junk ANDs at indices10,15, no equal fulltruth columns. It is invalid and was sent to the exact-SAT agent for bounded repair. Independent audit: near-false-positive-audit.json.

Every45-second run saves complete stdout/stderr. Exact counts/source hashes are in validation.json. Compile warnings in search-balanced.cpp are only indentation style at the one-line guarded continue; compilation succeeded. No tracked file was changed by this search.

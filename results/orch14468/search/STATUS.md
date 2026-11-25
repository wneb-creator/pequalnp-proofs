# L-meta-14468 search and independent certificate audit

The exact10-gate, exactly-one-NOT synthesis run returned UNKNOWN after119.2 seconds. It used all256 truth rows,7,960 variables and110,429 clauses. The model has eight raw inputs, strictly earlier references, binary AND/OR, unary NOT, all inputs used and all internal gates structurally used. This run establishes no lower bound and found no witness.

Encoder diagnostics passed: the pinned11-gate monotone baseline and a pinned14-gate circuit with an active but redundant NOT were SAT and independently checked on all256 assignments. Changing the baseline's final OR to AND was UNSAT. Complete CNFs, partial LRAT output and unabridged diagnostics are archived in the two ordered `search-artifacts.tar.gz.part01` and `.part02` files; concatenate them to reconstruct the complete archive. `ARCHIVE_PARTS.json` records the archive and part hashes, and the adjacent per-file manifest records every archived file.

The public PR18915 source was independently audited using a separate scalar Python implementation, not the Lean checker. The audit reconstructed all166 signed live-frontier states and checked all27,472 binary/retention moves, including222 exact hashed child links. It also checked the512-row target table and variable permutation, the152 positive/negative separator pairs, all eight essentiality witnesses, the three-input fixing lift, and the11-gate monotone witness on all256 assignments. Every check passed. The public source's semantic proof is being checked separately by Lean; this audit does not substitute for that proof.

See `audit_public_certificate.py` and `public-certificate-audit.json` for exact source provenance, hash and counts. No solver process remains active, and no counterexample was found.

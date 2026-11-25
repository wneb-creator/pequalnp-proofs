# Counterexample search record for L-meta-9811

No circuit of at most 24 gates has been found. No general UNSAT certificate has been obtained. Search timeouts are UNKNOWN, and all construction templates are restricted searches.

The known exact witnesses are baseline25.json (25 gates) and star27-dual.json (27 gates with one NOT). The files best.json, best-pair.json and best-ordered.json are incorrect approximation seeds, not proofs or counterexamples. Their mismatches are recorded in the logs. Smoke-test logs that say FOUND concern the known 25-gate positive control.

The Python sources and complete solver logs are preserved here; large generated CNF files remain in scratch and can be regenerated from the saved source snapshots, schemas and row lists. Source scripts retain the original scratch paths. MANIFEST.json records SHA256 hashes of the preserved files.

compact_hybrid.py expands each selected abstract construction into ordinary AND/OR/NOT gates and checks every one of 16,384 input assignments before accepting a witness. A NOT template uses counterexample-guided refinement; monotone boundary samples alone are never treated as complete for NOT circuits.

The dual helper computes g as an OR of earlier wires once, then exposes both g and NOT g. The count of selected wires T gives exactly T-k-1 primitive gates for k AND nodes. All gate counts refer to the explicit expanded circuit.

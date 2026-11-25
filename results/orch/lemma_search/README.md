Lower-bound certificate research for L-meta-9811.

Lower9811-heavy.lean compiled with Lean exit 0; full output is lower-heavy-build.log. It proves only a lower bound of 20, while the posted target is 25. Source SHA256: b98aba4e4e627860522f3ea1e52ebab14e0284452d776f97fb88b6f1cd1b5c42.

The DP attains 17 with basic restriction rules, 20 with the reader rule, and remains at 20 after adding 268 existing graph bases or testing all 30 opposite-partition nonedge quotients. Programs are preserved as originally run; their scratch paths are explicit in source. The generated certificate uses 136 canonical graph states and 3 reader nodes.

Dnf9811.lean and Support9811.lean independently compiled. A lighter DNF-based certificate is under validation.

The preferred Lower9811-light.lean also compiled with exit 0; full output is lower-light-build.log. It replaces propositional equality search with finite DNF subsumption certificates. Exact hashes, sizes, line counts, and exit codes are recorded in validation.json.

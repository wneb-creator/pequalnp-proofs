# Exact-hypothesis punctured-Fano CGP

`punctured_fano_cgp.cpp` reads `punctured-fano.input` as data. That file is derived from the independently checked `fano_minus_incident_pair.json`: Fano incidence (point minus line modulo7 in{0,1,3}), with point0 and line0 removed, remaining inputs reindexed. There are6points,6lines,16edges, minimum degree2, no4cycle, and a diagonal perfect matching; vertex-cover number6. The canonical point-star circuit has21gates, so the search targets at most20.

All4096assignments are evaluated. The same reviewed joint-cone logic retains output ancestors and sufficient semantic pure-star witness cones, including unused/post-outputwitnesses. The emitted circuit has exactT0 and counts all retained gates. Greedy witness selection is a size upper bound, not an optimality or lower-bound claim.

`verify_punctured_fano_cgp.py` independently reconstructs the deleted Fano graph from the modular incidence formula, compares it with JSON, enumerates vertex covers, and fully validates every printed circuit, raw OR reach and semantic star witness.

Controls passed: canonical21; DNF31 with10necessarypost-outputstarORs41; duplicateANDline-shield guard39. A2-second smoke run attempted1,479,376mutations across6restarts, accepting618,726; best remained21. Complete logs are archived as `punctured-cgp-*`. No long run starts before independent review and root renewal.

Usage: `punctured_fano_cgp graph.input seconds seed capacity control-only`.
Verification: `python3 verify_punctured_fano_cgp.py fano_minus_incident_pair.json output.stdout`.

The independently reviewed480-second run finished normally at2026-11-25 16:15:19UTC:336,751,024mutations,1,348restarts,140,751,528acceptedmutations. Minimum remained21gates(6AND); no≤20candidate. Every emitted circuit passed complete4096-row validation. This is heuristic search evidence only, not an UNSAT or lower-bound proof. Complete logs and metadata are archived as `punctured-cgp-search480*`.

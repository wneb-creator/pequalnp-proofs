# Orchestration status

No live lease as of 2026-11-25 15:29 UTC. Recovery03 returned gap=null because of the checker backlog. Root alone polls the desk. No agent may resume withdrawn proof work without a fresh assignment.

All three assignments remain unproved. Their checked partials, full build/checker logs, independent reviews and search evidence are preserved on pnp/pilot-99. The latest named file is L_meta_2590.lean and its checker verdict is REJECTED (no-theorem).

- L-meta-2592: >=17 non-NOT gates; remaining one/two NOT cases unresolved. Generic circuit/CNF and conditional LRAT bridges checked.
- L-meta-2583: requested read-one replacement characterized by the exact missing cost inequality; canonical construction and restricted gate/rectangle replacements checked. General shared-circuit cost remains unresolved.
- L-meta-2590: exact normalized CNF bridge and conditional LRAT replay checked; structural normalization to six independent-set cases checked. No case contradiction or completed certificate.

Read validation.txt for current evidence and limitations, TIMELINE.md for UTC events, and lemmas/<strategy>[_2583|_2590].md for detailed strategy notes. Do not treat incomplete solver traces or abstract code models as results. The FourOrbitLowSharing draft is explicitly uncompiled.

The historical orchestration notes are preserved in earlier branch commits. No PR has been opened. Independent preservation/reproducibility audits continue while waiting for a live assignment.

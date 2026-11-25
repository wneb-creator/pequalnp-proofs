# Lower-bound investigation

Started 2026-11-25T17:31:21Z.

Target truth table: `0xfeeefeeafeeeccc8`. Minimal true sets: 01,12,13,04,14,234,05,235. CNF clauses: 145,0234,013,012.

A nine-gate monotone upper bound is:
- 6 = x2 AND x3
- 7 = x0 OR 6
- 8 = x4 OR x5
- 9 = 7 AND 8
- 10 = x0 OR x2
- 11 = 10 OR x3
- 12 = 11 OR x4
- 13 = x1 AND 12
- 14 = 9 OR 13

All 64 truth-table entries agree by independent Python arithmetic. This is not yet a Lean-checked lower bound.

No exact matching truth-table halves occur in current Outside files. Searching all 720 permutation/dual orbit tables against 438 six-input/encoding candidate files found no existing equivalence.

Example lower-bound search engine `L_meta_12132.lean` is 3814 lines and carries bespoke precomputed data (input masks, finite search certificates). It could be copied and specialized but needs a search/certificate generator. `PEqualNP.Defs` exposes LRAT encoding definitions but not the soundness bridge theorem; permitted imports do not currently include Library/LRAT.

## Independent reference-proof review

The positive twin proof restriction tree is correct:
- Set x5=false, then x2=false and x3=false: majority(x0,x1,x4).
- Set x5=true, then x0=false and x4=false: majority(x1,x2,x3).
- The first restriction removes two normalized binary gates on one branch; the next two each remove one. Majority of three needs four AND/OR/difference gates. This gives a lower bound of eight normalized binary gates. A circuit containing any NOT thus has at least nine total gates, and the nine-gate monotone witness suffices; a NOT-free circuit serves as its own replacement.

Independent finite verification 2026-11-25T17:33:54.949566+00:00
Both restriction leaves equal three-input majority on all 8 inputs.
Normalized binary program states with target 232 absent: [(0, 1), (1, 12), (2, 114), (3, 994)]

Outer guard on Refutation.lean passed. Exact final statement checked as the negation of the desk statement. This refutes the assigned negation, not a check-mode proof.

# Independent checkpoint reviews

These verdicts cover owner-authorized research checkpoints. They do not establish a posted gap or acceptance by `tools/check-lean.mjs`. Reviewers checked the exact sources and scope claims, manifests, complete validation logs, forbidden proof constructs, and credential patterns. No matching credential content was emitted or archived.

| Checkpoint | Independent reviewer | Verdict and scope |
| --- | --- | --- |
| `f5f2fbbc8a4147e08f72c174487f3a25f7a8a31e` | formal_audit | PASS: exact 5 staged files. `Windows.lean` matched the compiled and reviewed source; complete log empty; partial scope and checker NOT RUN documented. Audit provenance corrected before approval. |
| `ff8e00765e26b6f603cebee98bdfea8ebfc96f0b` | formal_audit | PASS: exact 37 staged files. Source/log copies and manifest hashes verified. The small-window result explicitly assumes `y.card ≤ 2`; its axiom audit lists only `propext`, `Classical.choice`, and `Quot.sound`. |
| `a40e5780a5ed63f203feb427232d3f1d22d34af7` | formal_audit | PASS: exact 113 staged files, 43 Lean source hashes and 43 successful logs. RunTrim's final blank lines were removed, the archived source recompiled successfully, and changed hashes/provenance rechecked. Source and documentation whitespace check passed. |
| `75b8164f35adb5d85732dbffc57f6c64603e090d` | lean_setup | PASS: exact 72 staged files, 67 manifest artifact hashes, 62 original-scratch byte matches, and 15 successful source/log pairs. All 459 whitespace findings were original `c ` separators in 9 raw solver logs; preserving those bytes retains complete evidence. |
| `d90164bce2bc07c579324d6692cbe7c982b22f71` | prior_routes | PASS: exact 58 staged files; all 16 relocated Lean compiles exited 0, and source/log hashes matched. Documentation links were corrected and rechecked. The already-pushed fresh subtree was excluded. |

The formal_audit archive was reviewed by lean_setup, independently of its author. [Archive review](reviews/formal-audit-archive-review.json) and [exact staged review](reviews/formal-audit-staged-review.json) preserve the reviewed hashes and scope.

No full posted-statement proof exists. A source may compile while proving only a conditional helper, a special case, an upper construction, or a counterexample to an auxiliary argument. Each directory states that distinction. Solver UNKNOWN runs and restricted UNSAT results are not target proof certificates.

The fp3_strategy archive was reviewed independently by prior_routes. [Review](reviews/fp3_archive_review.md), [source hashes](reviews/fp3_archive_review_sources.json), and [exact staged bundle](reviews/fp3_archive_review_bundle.json) preserve that verdict. The bundle content-list SHA256 is `0a835ea841275d875592268da653acbd667936f4c6607fd58380b4bda152279f`.

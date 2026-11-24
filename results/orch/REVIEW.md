2026-11-24T05:27:26.818851+00:00
Independent pre-push review: L-meta-1422

Reviewer: independent_review
Verdict: PASS for source transformation and plain-file checks; compilation and kernel verification pending.

Candidate: lean/PEqualNP/Outside/L_meta_1422.lean
SHA256: 50c5b999ad95b7fbaf4089544fb4bf600203a3c25b102979f226d8fcda16dc76
Size: 72,060 bytes; 1,345 lines; regular UTF-8 file, nonexecutable.

The complete candidate was compared with upstream L_meta_1421.lean, accepted and merged through PR #2958 at commit 2855f75f83a4aaedaf14406b199d21f6ad33cb8b. The only changes are the auxiliary namespace rename, target theorem rename, exact negation of the assigned statement, and the two proof lines intro h / apply h. Every helper definition, lemma, finite certificate, and original proof step is otherwise byte-for-byte unchanged. Existing source attribution and Apache-2.0 notice are preserved.

The candidate theorem type is exactly the negation of the desk statement. The desk statement itself is exactly the negation of the accepted upstream theorem. The wrapper is mathematically valid double-negation introduction and adds no axioms.

The repository's actual checkImports and checkOwnNamespace functions both pass. Imports are only Mathlib and PEqualNP.Defs. All helpers are in the file's own auxiliary namespace. The guard checks prohibited text, including quotes, _root_, forbidden commands, attributes and options; no violations were found. No new imports, data types, instances, or proof mechanisms were introduced by the transformation.

PR scope must remain exactly this one added Lean file. results/orch artifacts must be absent from the final PR tip relative to upstream main. The current working tree also has untracked results, which are authorized preservation artifacts, not part of the proof PR.

Submission caveat: this is a refutation, not a proof of the posted claim. The local checker must be run with refute. The desk row currently defaults to check; outside-guard.mjs lines 110-114 rejects a refute run against such a row. Do not represent local refute acceptance as proof acceptance or guaranteed PR acceptance. Build and checker results remain to be established in the pinned environment.

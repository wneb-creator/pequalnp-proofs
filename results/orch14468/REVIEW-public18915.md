# Independent review of public PR 18915 adaptation

Reviewed 2026-11-25T18:14:04.754857+00:00. Verdict: PASS for source provenance, exact interface, formatting, and preservation.

Source: `results/orch14468/lemmas/Public18915.lean`, SHA256 `5c0f4a872ef18607dfa4be1c150020e256eff4df564c55e8898fdc47bd42f124`, 112661 bytes, 2222 lines. The named `lean/PEqualNP/Outside/L_meta_14468.lean` is byte-identical at review time.

The public proof is by Leg0shii, PR https://github.com/brilliant-hq/pequalnp-proofs/pull/18915, pinned head `c63b1058c3fe975a0c152a1b88930e9c6f41c837`, source SHA256 `81cc0c084c6e6374795ee8f2dfa86c517c61cb34434911ba54cf6b2f1bd53c74`. A full byte diff confirms only removal of the redundant Mathlib import and addition of an attribution comment; all declarations and proofs are unchanged. Public status was OPEN with no reported checks at discovery; this review does not treat that status as remote acceptance.

The final theorem type matches the desk's complete statement text exactly, including the arbitrary gate list, fan-in bound, at-most-one-NOT premise, default-read semantics, and no-larger monotone replacement conclusion. The final proof actually derives a stronger ten-non-NOT-gate floor for unrestricted NOT usage. A circuit already containing no NOT is returned unchanged; otherwise that floor plus the existing NOT yields at least eleven total gates, permitting the explicit eleven-gate monotone construction. The independently assigned mathematical/certificate review is recorded separately by lower_bound.

Format scan passes: only `import PEqualNP.Defs`, no forbidden root substring, string literals, sorry/admit/native_decide/new axioms, unsafe/elaboration escape declarations, or attributes; all sixteen options are scoped maxRecDepth/maxHeartbeats settings. The file is below 512 KiB. The declared namespace and final full theorem name match the assigned gap.

Author reported successful Lean compile/export with exit 0. Complete archived stdout was read and contains warnings only; stderr is empty. No independent compilation was repeated. Root's named lake build and official local checker are separate validations, pending when this review was written. No claim of remote acceptance or new authorship is made.

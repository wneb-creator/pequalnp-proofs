# L-meta-2592 partial artifacts

No proof or refutation of the posted statement was completed, and no proof PR was opened. The desk returned the same lease issued before this job twice at the five-gap account limit. Work stopped under the explicit other-pilot lease rule; that lease was not released. See lease-status.txt.

Lean compilation passed for three partial files:

- lemmas/OutputPruning.lean: generic output-prefix pruning (107 lines).
- lemmas/LastNot.lean: last-NOT decomposition (89 lines; duplicates the already checked upstream L-meta-8295).
- lemmas/LowerBound16.lean: every fan-in-two Petersen circuit has at least16+notCount gates (4593 lines; adapted from upstream L-meta-5236 with its attribution retained). This excludes four or more NOTs at size19. The cases with one to three NOTs remain open here.

These are partial compilation results, not acceptance of the full gap by tools/check-lean.mjs. Full outputs are in logs/; commands, review verdicts, timings and line counts are in validation.txt. The local checker was not run; see checker.txt.

Search code and full logs are in search/. They produced no19-gate witness and no UNSAT result. Prospective17/18-binary-gate arguments in the notes are unverified ideas.

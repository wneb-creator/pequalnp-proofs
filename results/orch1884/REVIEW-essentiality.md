# Independent review of InputEssentiality and polling archive

Reviewed 2026-11-25T15:40:19.153568+00:00

Source: `results/orch1884/lemmas/InputEssentiality.lean`, SHA256 `c4b010fe68ff746b09f3f7fa40edc9a7b83471e23f7626ef2af1b9d797f145e2`, 2641bytes, 64lines. Reviewer: status_check, independent of the author.

Verdict: no mathematical, format, or credential-content issue found. Suitable for honest partial-result preservation after the reported successful compile. It does not prove the posted1884 lower bound and is not by itself a proof PR.

The target is exactly the15-edge Petersen Boolean function. Finite witnesses show singleton inputs are false and each selected neighbor pair is true. If any nonzero vertexv is absent from the input mapπ, those two assignments have identical mapped inputs; becausev≠0, they also have identical extra unary inputu(x0). A deterministic circuit cannot distinguish them. Thus every nonzero vertex must occur. The counterexample corollary is its classical contrapositive, and the last lemma adds explicit coverage of0 to obtain surjectivity. The argument correctly makes no gate-size or gate-basis assumptions, so it also covers degenerate circuits. It does not infer coverage of0 without the additional premise.

Source imports only Defs and keeps all declarations inside the target subnamespace. No `_root_`, quotes, sorry, new axioms, native_decide, code-execution commands, disallowed attributes/options, credentials, or external executable content found. Source is far below512KiB. The captured compile stderr is empty; stdout has only one unused-simp-argument warning for Function.comp_def. That warning does not affect validity, and I did not rebuild because no concern required it.

Polling archive review: `null-responses.jsonl` contains exactly two complete public desk-null responses, attempts4 and5 at15:27:18.947805UTC and15:31:18.948146UTC. Both state checker backlog, include queue counts and retry_after_s600, and contain no lease ID or credential. `matching-paused.md` accurately labels a partial27-record read-only search and explicitly avoids an exhaustive no-match or have=proof claim. No issues found.

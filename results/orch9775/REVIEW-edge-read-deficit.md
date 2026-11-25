# Independent review: EdgeReadDeficit

UTC: 2026-11-25T17:29:42.165050+00:00

Verdict: PASS for the stated conditional helper. Source: 55 lines, 2,273 bytes, SHA-256 `b2ae397380d4892eec92a24d1b662e447f138b3cadc9954f8d4b23f51d26c678`.

`all_edge_reads` uses exact function equality to show every prime implicant is one of the posted edge pairs. An accepting assignment contains an edge; that pair is an accepting subset, so prime-implicant minimality forces equality. The finite edge-order fact supplies the ascending list required by ReadK.setList, avoiding any pair-order mismatch. This lemma needs no circuit normal-form assumption.

`deficient_edge` takes the full strict IsAO2 hypothesis, exact target correctness, and size at most 24. If every posted pair passed the joint readsAtMost test, the previous lemma would give semantic ReadK1, contradicting the independently reviewed ReadOneFloor lower bound. The conclusion is the existence of a specific posted edge with joint readsAtMost false. It does not replace this joint criterion with independent scalar minima, and it does not prove the unrestricted posted statement.

The exact source hash matches the author validation record. Both archived complete success streams are empty; Lean export exit 0 is recorded by the author. No build was repeated. No prohibited proof markers, strings, attributes, or options occur. The ReadOneFloor dependency import remains a research-helper integration caveat: standalone submission requires inlining and rebuilding the allowed source closure.

# Independent final archive audit: withdrawn L-meta-2590

Reviewed 2026-11-25T15:25:52.594983+00:00 by sat_encoding. Verdict: PASS for preservation as stopped-search evidence and controls; no completed proof or circuit refutation. No new solver run or mathematical search was performed.

Frozen final manifest `gap2590/counterexample/final-manifest.json`, SHA256 `3176ec4845271e270627ae2e64f98111a49e9519ca5d74a8be81a6ca33b0fbbc`, lists33 files totaling576652bytes. Every named file matches its size and SHA256. The earlier13-file frozen manifest was independently reviewed by status_review and is unchanged.

Read-only audit script `gap2590/sat_encoding/review_final_archive.py`, SHA256 `d73ccb53ae18395a53553a028ac2dd540443c4a9ebf97115b96dbd536d151e09`, exited0. Complete output is in `review-final-archive.stdout/.stderr`; stderr is empty.

The complete baseline solver log records caught SIGINT, UNKNOWN, then raised SIGINT. It contains no SAT or UNSAT result. Agent/manifest report shell exit130. The separate1,689,837,568-byte unfinished LRAT prefix is excluded from this small manifest; I did not open, pack, or validate it. The prefix-format JSON only samples10000 events/7397 additions with no negative hints; this is not a validity check or certificate.

The abstract code model is a static set system, with12 active slots,20 memberships,8 complementary pairs, and12 false-positive graph pairs. I independently verified its recorded abstract constraints. It has no Boolean gate list or output and is explicitly not a circuit or refutation of the leased statement. Code-cycle enumeration is archived as an abstract finite experiment, not evidence of circuit realizability.

Both positive six-AND skeleton controls were independently evaluated on all1024 inputs and their saved SAT models satisfy every recorded CNF clause (11346 and11406 clauses). They compute the Petersen edge function in the free-OR skeleton semantics. Their raw-read counts are `[3,1,3,1,2,1,2,2,3,3]`; naive expansion into binary gates costs20 (six ANDs plus14 ORs), so these are positive20-gate controls, not19-gate counterexamples. The final script includes disjoint raw-input sides; the earlier baseline CNF has60 fewer disjointness clauses, and the preserved CNFs establish the exact tested formulas.

The negative read-two control fixes the SAME three-read star construction, then imposes an at-most-two raw-read bound. I checked that every selector/output is fixed to that construction and found the explicit contradiction: selector variables11,32,107 are all unit-true while their all-negative triple is an at-most-two clause. Its UNSAT result is only a negative-control check. It does not rule out other six-AND read-two skeletons or any≤19 circuit. No free7–10 search probes were launched according to the frozen manifest.

Approved for root preservation: all33 named final-manifest files, this manifest, this report, the independent audit script, and its complete stdout/stderr. Keep the raw unfinished LRAT prefix labeled incomplete if separately retained.

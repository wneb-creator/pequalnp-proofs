# Independent review: paid insertion frontier and shared cover

Reviewed by constructive on 2026-11-25 UTC. Stable source: `/tmp/oec/pequalnp-pilot-70/formalization/frontier/SharedCover.lean`, 394 lines. Read the complete source and the empty `shared-cover-check-3.log`; the author reports Lean exit 0. This review did not rerun Lean.

Verdict: PASS for the stated abstract lemmas, including the repaired shared gate accounting.

`pair_hit_boundary` correctly descends accepting OR parents while preserving the missing-singleton-endpoint conditions. Positive-support ANDs are excluded by the explicit empty-AND-support hypothesis. A selected empty child belongs to the image defining the frontier, including the asymmetric second-parent case.

The modified `coverCert` copies the nonempty child at insertion ORs. Its omitted empty child's local certificate lies in the fixed global union T. The induction proves a local hit or a hit in this fixed T; it does not assume that T already covers the omitted child's pair hits. The earlier-child induction hypothesis supplies that fact, avoiding circular reasoning. Every boundary root is earlier than N and has empty support, so the final shared coverage follows.

The DAG union budget charges only `small minus insertion`. Distinct boundary roots cost at most the number of insertion ORs by the image-cardinality inequality. The final identity combines these into the cardinality of `insertion union small`, counting overlapping size-one insertion gates once. `reserved_not_growth` then excludes every reserved gate from the large strict-growth OR class. This is the precise correction missing from the initial informal sum of the two budgets.

The final `positive_shared_cover` is simultaneous over all positive-support roots in the modeled prefix. It assumes the abstract parent-support condition at every AND, as well as empty AND output support; a clean C4-free circuit prefix must separately supply those hypotheses. It does not handle the exceptional dirty gate or prove the final Heawood lower bound.

The forbidden-format scan returned status 1 with no matches for `_root_`, string literals, attributes, `sorry`, axioms, `native_decide`, or options. The import is `PEqualNP.Defs`.

# AND lower-bound specialization

FULL FILE STATUS: UNCHECKED.

AndLower.lean specializes the accepted upstream L_meta_217 generic theorem to the exact Petersen-minus-vertex function. Its first local Lean run failed only in the new suffix; the copied generic proof elaborated without errors. The suffix has been repaired, but the full file has not been rerun. Do not describe this file as a checked AND lower bound.

AndFacts.lean checks the finite graph facts and gate-index count bridge separately. Its specialized theorem explicitly assumes the generic lower-bound theorem as a hypothesis; it is not an unconditional AND lower-bound proof. The final short run completed at2026-11-24T15:41:47Z with EXIT0 and empty stdout/stderr (facts-build-4.stdout/facts-build-4.stderr). The finite graph facts, count-index bridge, and conditional specialization theorem are checked. This does not establish the unconditional full-file theorem without the accepted generic proof, which has not been rechecked together with this suffix.

Upstream provenance: commit2646e587870a2bf8dea22c866e757d4e88cf6193, PR2853, checker ACCEPTED(exit0): https://github.com/open-goat/pequalnp-proofs/pull/2853#issuecomment-7115695679 . The copied generic theorem and helper proof are unchanged except namespace/name/placement. Current source uses Mathlib and PEqualNP.Defs imports.

Commands ran from lean/ after sourcing /tmp/oec/pequalnp-pilot-32/tool-env.sh:

    lake env lean /tmp/oec/pequalnp-pilot-32/and_lower/AndLower.lean
    lake env lean /tmp/oec/pequalnp-pilot-32/and_lower/AndFacts.lean

Full original stdout/stderr are retained as build.stdout/build.stderr and facts-build*.stdout/facts-build*.stderr. No local checker was run for these supporting artifacts.

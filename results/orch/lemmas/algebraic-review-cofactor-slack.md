Independent review by algebraic_route

Source: structural-cofactor-slack.lean
SHA256: 944a32436f5e97e368f030a1e9636ec848bc3ee031ce80d2da4f998594117741

PASS. The first 5846 lines match the accepted source after namespace renaming. The new proof applies cof_core only to branching cofactor wires, whose surplus equals totalSurplus. A kept original unit mapped to a nonbranching wire contributes at least one to cof_sur but is absent from that restricted preimage sum. Erasing its original wire gives the strict extra unit without assuming injectivity of the cofactor map. The ineligible-label corollary correctly transfers singleton support through cof_Inv and forces the image wire to have fanout at most one. Full standalone logs are empty; author reports exit 0. No forbidden trust or format markers occur in the new tail.

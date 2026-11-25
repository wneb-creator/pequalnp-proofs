# Independent review: algebraic equality low cases

Verdict: PASS for partial preservation, conditional only on the reported Lean exit0.

Frozen file: results/orch/lemmas/algebraic-equality-low.lean
SHA256: 6d9d2a2802b8481386440105805dceb07fea521c52c3e842a1df8aa0997764fb
Lines: 6,827. Source prefix through line6,745 matches accepted L6659 exactly. The namespace is still PEqualNP.Outside.L_meta_6659_aux; it has NOT been renamed, and must be renamed or intentionally merged before use in another step's final PR. This does not block archiving the partial.

Reviewed all80new theorem lines and the invoked statements hw_count,hw_lost,os_union,mx_star,tight_surplus. For q6or7, all7 opposite-side labels are eligible; Oc/Mi partition the7 neighborhoods; Iq comprises q ineligible points. hw_count gives Bplus ≥14−2|Mi|+|union(Mi)|, hw_lost gives Bzero ≥|Mi|−(7−q), and os_union bounds that union by min(|Mi|+2,7). The cap {0,1,2,5} is contained in Iq, so mx_star gives Bplus≥eligibleCount+3. These force Mi empty,Bplus14,Bzero0 under totalSurplus≤14.

Independently enumerated all bounded integer possibilities q∈{6,7},0≤|Mi|≤7,0≤|Mi∩Iq|≤|Mi|,0≤union≤7,0≤Bplus,Bzero≤14 under exactly those inequalities. The sole feasible tuple for bothq is (Mi0,intersection0,union0,Bplus14,Bzero0).

Complete build stdout/stderr exist and are empty. No forbidden _root_,string literal,sorry,native_decide,oraxiom declarations found. This theorem does not claim the full27-gate refutation or derivative preservation.
2026-11-25T10:40:54.447932+00:00

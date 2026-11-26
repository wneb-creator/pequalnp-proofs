# Named helper export audit

The earlier helper passed its proof and axiom checks but exported six lazy
equation theorems under imported namespaces. The ordinary full-proof checker
permits identical imported theorem duplicates through `sameTheorem`; its
blanket extra-declaration rejection applies to reductions. The earlier census
therefore did not establish a full-proof checker rejection.

Two local reflexive lemmas now
avoid those exports; all 42 original lemma statements are unchanged.

The canonical Lake build passes. Inspection of the actual compiled module
finds 116 kernel declarations, all within the helper namespace. Its 142
compiler-only extra names include local specializations with library-name
prefixes; they are recorded separately and are not kernel declarations.
All 44 helper lemmas use only the three permitted standard axioms.

Complete build/audit logs and declaration censuses are included. The audit
scripts contain job-specific scratch paths; adjust those paths when rerunning.
No compiled library is included. This is an audit of the partial helper,
not acceptance of the exact posted gap.

Cut12 candidate certificate data for L-meta-670.

These data encode 4,734 states (555 expression wires) and the enabled states for
budgets12 through15, NOT counts0 through7. They are NOT a checked proof of the
posted lower bound. The row decoder has35 Lean kernel-checked representative
examples; complete row/wire reconstruction and hash lookup/automorphism checks
were performed independently in Python. The complete static finite replay is
still outstanding.

Files contain only public graph/proof data. Cut12CodecManifest.json.gz is the
frozen authoritative data manifest. Decompress it to Cut12CodecManifest.json
for the lookup validator. make_cut12_codec.py also reconstructs its own input
from this gzip when Nonprefix12Manifest.json is absent. Run generators from
this directory. They preserve the exact checked source/data bytes.

lookupStamp(k,t,h) indexes4,695 orbit classes. Thirty-nine classes contain two
state representatives used at different budgets; the small alias table chooses
an enabled representative. Semantic correctness must still be authenticated
by the Lean replay checker using actual state permutation equality.

No compiler trust, hash-injectivity assumption, or native_decide is used in
the eventual intended proof. Current Python validations are diagnostics only.

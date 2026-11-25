# Compact checked star-pencil classification and residual extension

The classification source shrank from 111,153 to **10,915 bytes**, with the same seven explicit hypotheses, theorem conclusions, options, and elementary corollary. Only its common integer denominator and polynomial combination changed. The exact multiplier identity now uses 244 terms and denominator 61,193,160, instead of 991 terms and an 87-digit denominator.

`StarPencilCompressedWithExtension.lean` also includes the independently reviewed residual triangle-extension lemma. `StarPencilCompressedAudit.lean` is exactly that combined source followed by three axiom-print commands. The full driver compiled successfully in **13.765645906001737 seconds**, sampled peak RSS **2,932,228 KiB**, under the serial 90-second / 4,096-MiB sampled monitor. All three theorems report only `propext`, `Classical.choice`, and `Quot.sound` in the complete stdout/stderr log.

Classification source SHA256: `fc97915621bef10f7bab6d5f77eeb8d566786fadc27fcca5d7b5d00896ad6963`.

The first theorem proves `r = 0` from seven displayed scalar equations; the second derives `p = q = r = 0` and `a = b = -1`. The residual-extension theorem derives `False` from five explicitly displayed specialized triangle coefficients. Geometric chart coverage, nonzero-parameter obligations, and the full gap statement are not silently asserted by these scalar lemmas.

Compression reused the already reviewed exact QQ engine as a linear-system solver on the known multiplier support. The 809-by-991 rational system solved in 15.865593661001185 seconds, peak RSS 830,192 KiB, with a 120-second / 2,048-MiB cap and one thread. The resulting proposed multipliers were then verified independently by exact `Fraction` polynomial convolution. An independent reviewer also parsed the actual emitted Lean expression, checked all 244 terms and normalized hypotheses, and multiplied the identity independently. The Lean kernel then checked the complete proof.

The archive includes the small exact certificate, final sources and driver, full build and solver stdout/stderr logs, generation/extraction scripts, mapping metadata, and independent actual-source review. The large intermediate linear-system input and basis remain in scratch; their hashes are recorded in `intermediate-provenance.json`, and they are not premises of the proof. The final certificate and Lean source are complete and self-contained for the displayed scalar statements. The original compiled archive and its successful audit remain unchanged in neighboring folders.

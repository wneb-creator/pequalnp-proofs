# Independent review: StrictNormalization

Verdict: PASS for the stated auxiliary normalization and deficient-edge
theorems. This is not a construction of the requested 24-gate circuit or
a refutation of its existence.

Reviewed source: `lemmas/StrictNormalization.lean`, 71 lines, 3,374 bytes,
SHA-256 `e2772f25e353b633c663001dd92aa6411f29836c8f3f546808889de01b96c6b2`.
The archived `strict-normalization-checked.stdout` and `.stderr` both
exist and are empty. The author reports successful checked compilation
and export. I did not rerun Lean for this read-only review.

`mono_size` faithfully embeds public `Monotone2` into `HasMonoSize`. It
does not silently assume strict binary gates, valid references, or a
valid output. The original model permits nullary/unary AND/OR gates and
the library's default values for unavailable wires; these remain within
the premise supplied to the existing cleaning theorem.

I inspected `LocClean.Clean.mclean_of` and its result type. It handles
the original circuit through the elimination invariant on every input
assignment, using default `Stat.const false` for unavailable references
and output. It preserves NOT-freeness and does not increase gate count.
Its constant-output branch is excluded by the explicit nonconstancy
premise. Here that premise is discharged for the exact 14-input target
using the all-false and all-true assignments. The proof does not restrict
the Boolean input domain to edge assignments or maximal negatives.

`clean_gate` excludes the NOT case using `NotFree`, leaving precisely
two earlier inputs and an AND/OR operation. `clean_ao` correctly converts
the indexed `CleanL` facts to the three components of `IsAO2`: AND/OR
operations, backward references, and exact input-list length two. Its
`getD` simplification is used only after a successful indexed lookup, so
no invalid-reference default is smuggled into the strict model.

`normalize` returns a circuit `D` computing the full target and satisfying
`D.size <= C.size`. `normalized_deficient_edge` applies the previously
reviewed `EdgeReadDeficit.deficient_edge` to this `D`, with its strict
model proof and the transitive bound `D.size <= C.size <= 24`. It does
not claim that the original unnormalized `C` has the same deficient edge
or the same squarefree derivations.

The source contains no `sorry`, new axiom, `native_decide`, forbidden
root-namespace marker, string literal, attribute, or option. This is an
auxiliary module importing another scratch module (`EdgeReadDeficit`)
and the library cleaning helper. Its compilation is not a final
single-file PR checker verdict; a final submitted file must separately
obey the posted statement and the repository's import/format rules.

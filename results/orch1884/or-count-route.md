# Read-only OR-count and bare-occurrence route audit

UTC: 2026-11-25T16:09:25.370731+00:00. No proof source changed and no solver run.

No checked unconditional Petersen OR-count floor of twelve or thirteen was found. Bounded searches selected451 files by nearby count/filter/OR syntax and9 files by explicit OR-count names; their relevant final-statement census contained106 records. The prior48-statement OR-count census was also consulted. This is a targeted textual search, not a proof that no equivalent theorem exists under another representation.

The closest general graph result L_meta_598 states nonisolated vertices <= OR-index-set cardinality + edge-containing connected components +1. For Petersen that yields only8 OR gates. L_meta_724 gives8 for a particular8-vertex graph. The familiar edge-count-minus-one result on pseudoforests does not apply to Petersen. General structural lemmas L4093/L4115/L8257 require girth at least7, while Petersen has5-cycles. The already independently validated23-gate/13-OR witness continues to rule out an unconditional14-OR floor.

L_meta_905 lines4666–4670 excludes a six-AND AndCountCircuit only when every input v belongs to leftVars i or rightVars i for at most two distinct AND macros i. This counts appearances in flattened OR operands, not physical source-reader gates. A source read once by q = x0 OR x1 can reach three different AND macros through a shared q, yielding three bare occurrences after the standard OR-cone flattening. This example blocks the proposed direct bridge from physical-reader <=2 to the L905 predicate. It does not refute a separate existence/normalization theorem preserving the AND budget; such a theorem would need its own proof and was not found here.

The original proposed ordinary-monotone18 route therefore has two unresolved obligations: a sufficiently strong OR floor, and a valid bare-occurrence bound after normalization. It also does not automatically cover free-negative-input circuits, since restriction of another input retains that supplied negative wire.

Complete selected-file lists and extracted statements are retained in scratch as1884-or-name-files.txt,1884-or-shape-files.txt,1884-or-fresh-statements.json, and1884-orfloor-candidates.json.

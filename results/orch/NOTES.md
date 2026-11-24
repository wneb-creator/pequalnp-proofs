# L-meta-5349 orchestration notes

Lease acquired 2026-11-24 23:11:49 UTC. Only root calls desk.

Goal: linear bound on Ustar witness subset S with all four role fibers at least 3, and disjoint opposite-side sets within each v-fiber. Girth at least 5, least AO, top form.

Strategies write separate notes below or their named files; scratch Lean belongs in results/orch/lemmas.

Final reduction: R_meta_5349_48, coefficient 27+5*d, local checker ACCEPTED (reduce). The local bounded-fiber premise remains unproved. Independent review approved the final147-line source. Complete validation and partials are retained in branch history; the PR tip must add only the named reduction file.

Root final case analysis: if every dirty witness contains a chosen endpoint v, the witness-cardinality lemma cannot apply. Aliasing the junk gate to input v can change other readers, so monotonicity and the selected-top data alone do not justify this simplification. This is another form of the uncontrolled-readers barrier.

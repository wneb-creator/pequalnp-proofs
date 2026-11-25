# L-meta-3773 reduced-core search

These are unsuccessful construction searches, not proofs or counterexamples.
The accepted reduction R_meta_3773_1 asks for a24-input core with at most58 gates and three outputs. Its main output is the incidence function on the graph obtained by deleting point9 and line0; the other outputs must equal two reserve ORs only where the main output is false. The direct construction has60 gates.

The dataset has45 positive edge tests and692 negative tests (737 rows total). The negative collection contains maximal independent assignments of the core, maximal independent assignments forbidding each reserve triple, and the six reserve singleton assignments. Monotonicity makes these sufficient to test the three requirements. Seed60 passes all rows. Engine opcode1 is AND and opcode0 is OR, unlike the separate Lean packed format.

Runs7901 through7906 each used120-second chunks. Versions1/2 search star-seeded DAGs; version3 increases positive-error weight; version4 uses a negative curriculum; version5 adds context-guided resubstitution; version6 starts with a23-gate dense overapproximation and adds negative tests gradually. Every saved candidate is independently replayed by geometry-meta3773-core-validate.py. All have errors. The best58-gate candidates each omit two required edges; they do not satisfy the gap or reduction. Run7906's best full-test candidate has48 gates and11 missing edges.

The scripts use bounded scratch computation and no network or credentials. Full search stdout/stderr is retained in the run logs. Build binaries are omitted; the C++ sources compile with g++ -O3 -std=c++17. Run an engine with DATA SEED SECONDS OUTPREFIX, using geometry-meta3773-core-data-v2.txt for versions2 onward. At most120 seconds is accepted. The source data generator writes files in its working directory; run it in a dedicated copy of this archive.

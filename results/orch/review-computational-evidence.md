# Independent computational-evidence review

Verdict: PASS for preserving the frozen computational evidence on pnp/pilot-51. These solver results are not Lean certificates and do not prove L-meta-3451.

The exact frozen set is the 89 files below, totaling 340639 bytes. All file hashes and sizes were independently verified against counterexample-review-manifest.json. Manifest SHA-256: 4b742218da9f9f7e54a91d530cd5ce6c224927007762c57f2e3f7a72d4d558f5. No running process or frozen source was modified.

## Encoding and completeness

The principal full-table, boundary, symmetry, ordered, and CNF encodings represent existence with at most the requested gate budget for valid nonempty incidence functions. They permit repeated operands (a <= b, not a < b). Start with a smallest witness, remove unused gates, put the output last, then append OR(previous, previous) copies to reach the requested budget. Every nonfinal gate still has a later consumer. Essential-input requirements are necessary. Input automorphism and adjacent independent-gate ordering constraints simultaneously retain a lexicographically least representative. The reduced variant permits a distinct-function active prefix followed by an explicit OR-copy suffix; duplicate-function elimination therefore does not prevent padding. The separate BFS checks every depth up to its bound, rather than relying on exact-budget padding.

The optimum-dirt queries are interpreted only at independently established minimum budgets. Removing unused gates could erase dirt in a nonminimal circuit, so those queries are not a general downward-completeness claim for arbitrary dirty circuits.

Boundary vectors consistently encode all positive edge inputs, all maximal negative inputs, and every clean-AND test. Monotonicity determines the function from the positive and negative boundaries. CNF export copies the reviewed ordered encoding and applies Z3 simplify/solve-eqs/bit-blast/Tseitin transformations to one goal. CaDiCaL SAT decoding validates the raw CNF model, converted original SMT assertions, and then the full truth table. UNSAT remains trusted solver/transformation evidence, not kernel certification. The free-constant C6 variant is a relaxation; its 17 packed rows were independently matched to the C6 truth function.

## Verdict accounting

- Complete essential N=4 unrestricted census: 25 results, exactly 14 UNSAT and 11 UNKNOWN; no SAT. Each tested budget is one below its independently verified clean construction. The summary matches every raw result exactly.
- N=4 clean census: 14 completed results, exactly 3 UNSAT and 11 UNKNOWN. Mask 34097 at budget 8 was started but interrupted, with no verdict. Its interruption record matches the raw log.
- Initial five-class full-table batches: all UNKNOWN in both modes. No lower bound follows.
- Four known-optimum singleton-dirt queries and four nonincident-pair-dirt queries: all UNSAT in the stated reduced model.
- C8 and nine-edge N=4 CaDiCaL 90-second trials: exit 0 / UNKNOWN. The later 300-second C8 run was interrupted without a verdict; the nine-edge retry never started.
- C6 solver/LRAT runs: raw logs report UNSAT and exit 20. The LRAT artifact was not Lean checked and is not included in this frozen set. Its size record is feasibility evidence only.

Independent replay checked all 334 N=3 clean witnesses, all 25 N=4 clean witnesses, and all six saved SAT models on every full Boolean input, including wire bounds and the applicable AND-clean conditions. All passed. The N=4 witness masks and sizes exactly match the census class list. Recorded source hashes resolve to frozen sources; earliest unversioned baseline smoke/benchmark results are calibration only. CaDiCaL trial provenance is recorded in the preceding CNF-export metadata.

## Publication scope

Selected source, structured records, and solver logs contain no credential access, authentication material, or live lease identifiers. NOTES.md and TIMELINE.md were also checked for lease capabilities. Notes distinguish computational evidence, partial Lean results, the axiom audit, and the missing official checker acceptance. The general statement remains unproved.

Reviewer: status_review. Review performed without changing proof or solver sources.

## Exact frozen files

| File | Bytes | SHA-256 |
|---|---:|---|
| results/orch/lemmas/c6-leanlike-benchmark.stderr | 0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| results/orch/lemmas/c6-leanlike-benchmark.stdout | 280 | e21ff37cb0f661fa1fa87ce47da85f91fc3956edce6e408c91c9e025e5e2b22a |
| results/orch/lemmas/c6-leanlike-cadical.stderr | 0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| results/orch/lemmas/c6-leanlike-cadical.stdout | 13778 | a4960815e13adb47275b2d7491d90a5a2656c816c868a781768a58785380ab2f |
| results/orch/lemmas/c6-seven-cadical.stderr | 0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| results/orch/lemmas/c6-seven-cadical.stdout | 9580 | 39bca026175d3d8273726a4fab12e60f2786d9f2d4a444a8d3f143b7b782ef54 |
| results/orch/lemmas/c6-seven-export.stderr | 0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| results/orch/lemmas/c6-seven-export.stdout | 466 | 6f3f24feafc0829e52480fcab217c44d20e92c167161f2c3c83b2e7d5e7245dd |
| results/orch/lemmas/c6-seven-lrat.stderr | 0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| results/orch/lemmas/c6-seven-lrat.stdout | 10085 | c342b1d576e76332446a97a0cb3d60bd98710676e0fed23d8a44223c13211b34 |
| results/orch/lemmas/c8-ten-300-cadical.stderr | 0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| results/orch/lemmas/c8-ten-300-cadical.stdout | 16608 | 3afea55708a5570d8d3c782821717ab0db5eee269062fee76b30a4d970b5a546 |
| results/orch/lemmas/c8-ten-300-trial.stderr | 0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| results/orch/lemmas/c8-ten-300-trial.stdout | 553 | 4f5abcf7a535f0996fc613a069e8b6de68e3788c806dce6ce70b74055038b8ef |
| results/orch/lemmas/c8-ten-cadical.stderr | 0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| results/orch/lemmas/c8-ten-cadical.stdout | 29463 | eb01f14a3c624c9c6cbb2811f8bba08b450b82ccc3c5ed67eb29967049df8dd3 |
| results/orch/lemmas/c8-ten-trial.stderr | 0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| results/orch/lemmas/c8-ten-trial.stdout | 821 | c100a8b763a860646189f76261a8785d0a2e0c3f8e1a1ff7cc1a53712dadace3 |
| results/orch/lemmas/counterexample_300_interruption.json | 253 | a7dc25625f5b683b18323e67ef9914067e54bdb8287d9eccc93c59f8a7efad0e |
| results/orch/lemmas/counterexample_c6_leanlike.py | 1556 | a01e056614237920f821ea055b39e12f2cbec4ecf4b93cfd2b9977432b7a0258 |
| results/orch/lemmas/counterexample_cadical_trial.py | 2877 | df306b8c3d17a2c5ae68c33efb2ac01f30e7cd30381a4ab4168246d686679221 |
| results/orch/lemmas/counterexample_clean_upper.py | 1936 | f115545e2033808c9e5867ffcaf622be4cb5ada86ebc95b8bb3ddb5076c6038e |
| results/orch/lemmas/counterexample_clean_upper.stderr | 0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| results/orch/lemmas/counterexample_clean_upper.stdout | 81 | a9535d3863057067ab15e784b44b48aae65cd43ee294eb2b45d0730302dc8ebe |
| results/orch/lemmas/counterexample_clean_upper_n4.py | 2022 | afe5b4c07356fcf32d00fb64f7af742f31c4fb0aabc3f499d837fa81fbf8de6a |
| results/orch/lemmas/counterexample_clean_upper_n4.stderr | 0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| results/orch/lemmas/counterexample_clean_upper_n4.stdout | 81 | c4ea71455f55fa9f250a4aa4216bcc14ec5b1f697f4fb1567c2dd447b7a09b2a |
| results/orch/lemmas/counterexample_clean_witnesses.json | 45124 | 727f534ffb29795b7b306dcc02317de2391b03b76bcfac023b52141274998b6c |
| results/orch/lemmas/counterexample_clean_witnesses_n4.json | 5144 | 650f30bc7e1d827a5c6fb3e29e52bbd3dfed5f8772101d21f280b3c511edbbc0 |
| results/orch/lemmas/counterexample_cnf.py | 3842 | 989747b15be25dc13e4484692339b10f85575e80907e782dd980ebdbb1d3142a |
| results/orch/lemmas/counterexample_cycles.py | 2375 | 17eb77c10a56c61410e7fb516c74dd5ddf8743fa5ee89bf2f5ff93d92afa3eb8 |
| results/orch/lemmas/counterexample_cycles.stderr | 0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| results/orch/lemmas/counterexample_cycles.stdout | 1535 | 8a283565df1ab09f0ed0ec367699d9ea80cc456ec8ca77fc460683547283c692 |
| results/orch/lemmas/counterexample_lrat_size.json | 484 | 5dc450cec1cf3255149ac3fbb059e6ebaee390984eeb9ce60c19642f116e9287 |
| results/orch/lemmas/counterexample_n4_summary.json | 3795 | b2cff0edde5be2810284fb96f26d27aa4147290526c5c144f2d9d9dbec631704 |
| results/orch/lemmas/counterexample_sat.py | 4197 | 2e8c8cbf19d705783169abedeeacfec6373e13cf0602179711dcdcce0d7d7323 |
| results/orch/lemmas/counterexample_sat_batch.py | 383 | 96a77eacd61c2fde5a6ec284bf938e61d026082e6e10a20ca5f6b2f966b52996 |
| results/orch/lemmas/counterexample_sat_benchmark.stderr | 0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| results/orch/lemmas/counterexample_sat_benchmark.stdout | 537 | a5ce5abd9f30e8230cf21c4d758378d64162bfa295266351b3f7819a941f70a4 |
| results/orch/lemmas/counterexample_sat_boundary.py | 6102 | 54c7aaaa29c9a87fefb763d53c3c2f3b1067f89691cee967ad936e74663259cb |
| results/orch/lemmas/counterexample_sat_boundary_benchmark.stderr | 0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| results/orch/lemmas/counterexample_sat_boundary_benchmark.stdout | 2251 | 0ffd54114bccca423d5366631d62e8fcd8f54f104e7944cbfac19c679f0cfa6a |
| results/orch/lemmas/counterexample_sat_boundary_n4_clean.stderr | 0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| results/orch/lemmas/counterexample_sat_boundary_n4_clean.stdout | 22589 | 5ba2ca83c755f40f5200d8b39149b2ed8eef4ca6bcba2e96cd1156dfe1c8e613 |
| results/orch/lemmas/counterexample_sat_boundary_n4_unrestricted.stderr | 0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| results/orch/lemmas/counterexample_sat_boundary_n4_unrestricted.stdout | 39279 | bf1ea346bffb64980fc9fb5800890bc241ef8783d7cf49b7bf7cdf2966a1d54d |
| results/orch/lemmas/counterexample_sat_classes.json | 1862 | e95600da0fcc9ce32b26ca63a89ec9384bbb0e2fb32444b49f5a677838b53501 |
| results/orch/lemmas/counterexample_sat_clean_interruption.json | 411 | 94342082b8a8fa7646797258944e577ee0ad1f3956622f40079a57c20bc9dbf8 |
| results/orch/lemmas/counterexample_sat_dirty.py | 6713 | a6af16c00151e9b28d4c0ea989e8d6ee8270e20aff9a8a266c786491e97050fe |
| results/orch/lemmas/counterexample_sat_dirty.stderr | 0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| results/orch/lemmas/counterexample_sat_dirty.stdout | 5025 | 8818b06b0361e8663d29a3e68800c627417db7c69a14c05bcaddcca9c9bb1159 |
| results/orch/lemmas/counterexample_sat_dirty_batch.py | 315 | e42fda972e15cb3d2f35de9e99f89f88065349025f37a90a89973355e612503b |
| results/orch/lemmas/counterexample_sat_dirtycross.py | 6765 | 068d52befcad1a88cf898f8be2bb729e3aea16efc6b83fd3fcf3ff038dc350b7 |
| results/orch/lemmas/counterexample_sat_dirtycross.stderr | 0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| results/orch/lemmas/counterexample_sat_dirtycross.stdout | 4891 | 4d278c302763a56e95970a4f7c3675ba6cede6a033343ecea9b191d629ab60e2 |
| results/orch/lemmas/counterexample_sat_dirtycross_batch.py | 320 | afd1e078198442cbd5dcbc0f45980a36bcf899a36e3075135d5db72ec190978d |
| results/orch/lemmas/counterexample_sat_fullbatch.py | 925 | 75952d77db7854c6b9d412325af6bd84483054eb012e0936edf1971c0fcd9b77 |
| results/orch/lemmas/counterexample_sat_n4_clean.stderr | 0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| results/orch/lemmas/counterexample_sat_n4_clean.stdout | 2145 | f57fd6988f06b37c225fc9d6d176b687bcc2dc7c8d65da8b4d7a1d5927c3b1db |
| results/orch/lemmas/counterexample_sat_n4_unrestricted.stderr | 0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| results/orch/lemmas/counterexample_sat_n4_unrestricted.stdout | 2155 | 456b6072934d021e86c0b07e079bcb92280e4653bcf9769c770e23e458fc0e10 |
| results/orch/lemmas/counterexample_sat_ordered.py | 6360 | 347652d7022336f75398299504e03992c6dd623cc2e2a030ea73fa20d43afa20 |
| results/orch/lemmas/counterexample_sat_reduced.py | 5776 | 4015ce3cf10aa18d8e5c81c467f458c19daf5854093944276972b08dfdc60913 |
| results/orch/lemmas/counterexample_sat_reduced_benchmark.stderr | 0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| results/orch/lemmas/counterexample_sat_reduced_benchmark.stdout | 2354 | c532389fcc21d9eba724ffc4e2ffa063ee86d1b3a9e6001dba2a6d7f75bc2da8 |
| results/orch/lemmas/counterexample_sat_reduced_smoke_source.py | 5761 | 7f34e9a445412b9e91411e566ea91f92c110f94bcc3a1bf9f25b317b6bdfb73f |
| results/orch/lemmas/counterexample_sat_smoke.stderr | 0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| results/orch/lemmas/counterexample_sat_smoke.stdout | 475 | 5f4a885d24180834dc7b8ecccb057bbc8b720175836f6b956a898203a683fa30 |
| results/orch/lemmas/counterexample_sat_sym.py | 5426 | 066a65ab395ce5ca80813f30af756ec1c6e4531b8178df333fdf5601ee72bfc7 |
| results/orch/lemmas/counterexample_sat_sym_smoke.stderr | 0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| results/orch/lemmas/counterexample_sat_sym_smoke.stdout | 1709 | 93e081c11beb155df09448565e0eb990bfe6c5994a0c8f4ceb293c00c9606959 |
| results/orch/lemmas/counterexample_sat_sym_smoke_source.py | 5411 | 4c56d013c98ee8624c4675aa53b48e8c4d3c40d093bd024a8a6cd18ae1dfd4c6 |
| results/orch/lemmas/counterexample_small.py | 2060 | 57c595251d34f7edeba13df34b2ebeb494715bd08f641e55648491699e4c98e2 |
| results/orch/lemmas/counterexample_small.stderr | 0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| results/orch/lemmas/counterexample_small.stdout | 805 | fc46bc507beb1c03d35fbd2c7a5bf12b7beaf4b2b2b191018ca26bfab876f6b8 |
| results/orch/lemmas/counterexample_three.cpp | 3852 | 3212989b770501a43c2228a1b64cd68e82678d16add423da47d2e91319a60bd8 |
| results/orch/lemmas/counterexample_three.py | 2164 | c737e472aa3ef3ef4a745bdaf31da9679088b46d724962a25a7c487972ee06e4 |
| results/orch/lemmas/counterexample_three.stderr | 0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| results/orch/lemmas/counterexample_three.stdout | 1862 | 124be0c89e0c704835cd296eaf49661ac27df44c11cb427abac8b512b7a487d6 |
| results/orch/lemmas/counterexample_three_cpp.stderr | 0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| results/orch/lemmas/counterexample_three_cpp.stdout | 1727 | 5d9a781cb8022362accf40f2ddf05371beb07ad809b98dc0ed3f867308b27a0b |
| results/orch/lemmas/n4-nine-eleven-cadical.stderr | 0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| results/orch/lemmas/n4-nine-eleven-cadical.stdout | 27265 | 3a695492cb6322e6c39d9c82aa45de31c8ed507327951a40a20ea506f26fceb5 |
| results/orch/lemmas/n4-nine-eleven-trial.stderr | 0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| results/orch/lemmas/n4-nine-eleven-trial.stdout | 834 | f406277000b5b1eef1fba1a4fa323f3b3d0526d17518866adc6bfb1c7dd9f968 |
| results/orch/lemmas/p4-cadical-smoke-cadical.stderr | 0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| results/orch/lemmas/p4-cadical-smoke-cadical.stdout | 6391 | 0d4f12a0935860c8448815d6612405b71614e7a7036eec90a956bbdb29f9e2cf |
| results/orch/lemmas/p4-cadical-smoke.stderr | 0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| results/orch/lemmas/p4-cadical-smoke.stdout | 803 | f78d78e1dfceea79ef0da8954972226edf491b41515487da79898f89900488d4 |

## Supplemental dirty-crosspair symmetry check

PASS. The frozen counterexample_sat_dirtycross.py at SHA-256 068d52befcad1a88cf898f8be2bb729e3aea16efc6b83fd3fcf3ff038dc350b7 enumerates only independent permutations within the two fixed sides and an optional global exchange of both sides. It does not independently exchange sides inside disconnected components. Every allowed map therefore preserves the set of nonincident crosspairs. Independently executed the selected pure automorphism function and checked exact nonincident-pair-set invariance for all four reported masks: (N2,7), (N3,417), (N3,426), and (N3,427), with respectively 2,2,2,12 automorphisms. The existence of a nonincident-crosspair-accepting AND is invariant under these symmetries. The original optimum-only scope remains in force.

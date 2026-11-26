This package accelerates the exact 1,024-row collision predicate used by the signed full-Petersen native search. It is a performance change to research code, not a Lean proof or a project-checker result.

The selected implementation is cached-collision.hpp, integrated by three small changes in signed-cached.cpp relative to signed-source.cpp. A parent profile records the values of its live wires on one assignment. A child deletes selected parent coordinates and appends one output. When at least one coordinate is deleted, replace the lowest deleted coordinate by the output bit and zero the other deleted coordinates. Equality of these sparse profiles is exactly equality of child wire values, independent of the child list's ordering. When nothing is deleted, the already separating parent guarantees separation. Scanning assignments in the original order preserves not only the collision verdict but the exact first witness pair.

The parent must have passed build() before child() is queried. Parent width must be at most 20, and deleted bits must be valid parent positions. The engine provides these invariants. The shared static table is intended for this single-threaded engine, as are its existing global wire tables. Stamp wrap clears the stamp table before reuse.

Validation:

* All 18 saved cap-17 frontiers, the complete wires.bin, and signed-collision-pairs.txt are byte-identical to the original child-collision engine. Exact hashes are in cap17-byte-identity.json.
* Both checked 20-gate constructions pass every cached collision and signed projection check; all 120 automorphism images agree on all 1,024 assignments.
* On 1,000 stratified cap-18 frontier-5 states, all 94,089 eligible children return exactly the original witness pair. There are 87,600 collisions. Original predicate time was 1.46283 seconds; cached time 0.083471 seconds plus 0.0191447 seconds for parent profiles, approximately 14.3 times faster including setup.
* On 100 stratified states, all 123,504 gate/retention combinations agree exactly, including combinations removed by earlier pruning tests.
* Synthetic states with widths 10 through 19 and shuffled parent/child order passed 17,920 further comparisons. Both forced stamp-wrap branches passed.
* signed_full_probe independently reviewed the selected header and its engine integration; no blocking issue was found.

The full cap-17 run took 21.43 seconds while other tests and searches ran concurrently; this is not a controlled end-to-end speed comparison. The collision microbenchmark isolates old and new predicates on the same eligible children. Pool construction and projection scans remain separate costs.

The larger profile-collision.hpp also contains an alternative that computes all 16 operation/retention outcomes for an operand pair at once. It is retained for the benchmark, but was slower on actual eligible children (0.193435 seconds), so it was not selected for the engine. It preserves exact witnesses too.

Reproduction requires the existing signedfull data generator/package: generate the same pools.bin and probe-data.hpp, place probe-data.hpp alongside these sources, and run with pools.bin in the current directory. Then compile with g++ -O3 -march=native -std=c++20 signed-cached.cpp -o signed-cached and run signed-cached 17 1 17 from a fresh output directory. Compile known-sanity.cpp and synthetic.cpp similarly and run them from a directory containing the same pools.bin. benchmark.cpp takes source-trace-directory, frontier-depth, original-budget, sample-count, and an optional all-combinations flag. The reported cap-18 sample used depth 5, budget 18 and 1,000 samples. Existing source traces are required only for these benchmarks; the complete cap-17 run starts from raw inputs.

No active search source or trace was modified by this experiment. The final collision cache can compose with independently validated projection-bucket changes.

Computational search for L-meta-2215

No witness was found. These computations are not a Lean lower bound or a Lean proof.

The complete monotone verification basis contains 802 output conditions on 756 distinct 25-bit inputs: 48 edge-positive and 553 maximal-independent-set-negative conditions for F; four singleton-positive and 197 maximal-independent-set-negative conditions for the auxiliary Q, with the four auxiliary lines deleted for the latter graph. Monotonicity makes this basis sufficient: edge and singleton inputs give lower bounds; every independent input extends to a maximal independent input for the appropriate upper bound. Q may contain additional edge terms; the search does not force it to be exactly the four-line OR.

Three stochastic runs tried 387260000 mutations in total. The first tried 147040000 mutations over 6842 restarts in 20 minutes; the second tried 150780000 over 6214 restarts in 20 minutes with auxiliary gates interleaved early and occasional uphill moves; the third tried 89440000 over 699 restarts in 12 minutes with counterexample-guided negative tests and rejected 722 training-perfect candidates. All best candidates failed exactly one full-basis condition. A separate exhaustive repair checked 206790 arbitrary single-gate substitutions and found no improvement.

best.txt fails only edge support {7,13}; F wire 82,Q wire 85. best-interleaved.txt fails only edge support {0,20}; F wire 85,Q wire 54. Each has 61 binary gates. The diagnostics files give exact failed rows and chosen outputs. Full run outputs are in the four .log files; summary.json records counts and SHA256 digests. No executable binaries need preservation.

To reproduce in this directory, compile with g++ -O3 -std=c++17 search.cpp -o search, then run ./search 1200 2215. The analogous second and third commands use search-interleaved.cpp with arguments 1200 3762 and search-cegis.cpp with 720 16137. Compile exhaust.cpp and pass best-interleaved.txt to the executable for exhaustive single-gate repair. data.hpp is generated from data.json and contains the input rows, classification masks and neighbor lists. stdout and stderr should both be redirected to a log.

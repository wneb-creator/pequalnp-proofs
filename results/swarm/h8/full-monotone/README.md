This is a monotone-only native search for the ten-input Petersen edge function with a budget of 19 binary gates. It is research code, not a Lean proof, not a proof of L-meta-2373, and not a project-checker certificate. The native search has closed the monotone 19-gate search space using only the checked upstream pool bounds described below. Formal replay and the unrestricted signed case remain outside this result.

The state model is the `Live false` contraction model used in L_meta_670. States contain distinct Boolean truth tables. Transitions add AND/OR results and independently retain or consume each operand. The target has all 15 Petersen edges. All 15 edge-minterm by 15 maximal-independent-set pairs are used for monotone separation. The 120 graph automorphisms identify equivalent states. Projected cofactor lower bounds and the existing kwCross/oneShare Horn/parity implications prune states. Both the search and the circuit-to-Live normalization still require formal Lean replay before a mathematical result can be called checked.

Pool provenance:

* Default: 2,997 distinct pools obtained by transporting the 434 distinct `moC`/`sgC` columns from checked L_meta_670 into all ten vertex-zero cofactors, plus the whole H9 monotone lower bound 16. Signed lower bounds are weakened to monotone lower bounds. Domains and augmented root functions are both transported. Duplicate domain/root pools keep the stronger bound.
* `--extra-6581`: adds 232 distinct pools, for 3,229 total, from checked L_meta_6581 `rootSCols`. Its signed H9 domain bounds are valid for the monotone search. Its witness encoding differs from L_meta_670; the generator uses its domains, roots and bounds, and does not feed its witness data to L_meta_670's `colCheck`.
* `--augmented`: adds 30 conditional pools granting an OR of two neighbours of the deleted vertex for free while retaining H9 bound 16. These depend on a separate native forced-OR H9 search that has closed computationally but has not been replayed in Lean. This option must be labelled conditional. The metadata records the dependency and an exact vertex isomorphism for every such pool.

Reproduce in an existing checkout containing the named upstream files:

```sh
python3 fullprobe_data.py --repo /path/to/pequalnp-proofs --output /tmp/fullprobe-run --extra-6581
g++ -O3 -march=native -std=c++20 -I /tmp/fullprobe-run fullprobe.cpp -o /tmp/fullprobe-run/fullprobe
```

Run the executable with working directory `/tmp/fullprobe-run`:

```sh
./fullprobe 19 1 1 > search.stdout 2> search.stderr
```

Arguments are maximum explored depth, whether all paid-prefix subsets may be considered, and whether the monotone factor cuts are enabled. A bounded-depth run may finish with a nonempty frontier: exit status alone is not an exclusion verdict. A claimed closure requires that the final frontier is empty, all earlier frontiers are accounted for, and no `TARGET PRESENT` report occurred. The source deliberately fixes `signedMode=false`; these data and factor cuts must not be used for an unrestricted signed search.

Optional fourth and fifth arguments resume a saved frontier in a separate output directory:

```sh
./fullprobe 19 1 1 6 /path/to/source-traces > search.stdout 2> search.stderr
```

The output directory must contain the same pool data, or an independently justified stronger set. Resume inputs must be the retained, complete trace of a preceding run. The loader checks wire-expression equations, input identities, IDs, and distinct sorted live lists. These checks do not themselves establish frontier completeness or provenance. See TRACE.md for binary formats. Large binary traces are intentionally not included in this source snapshot.

Validation completed before this snapshot:

* Independent scalar reconstruction matched all 2,997 default pools, all ten cofactor isomorphisms, all 120 automorphisms, and all 225 boundary pairs.
* Both checked 20-gate constructions L_meta_584 and L_meta_587 survive every pruning test on their live execution paths. Expression-DAG permutations match scalar evaluation on all 1,024 assignments.
* Compact paid-mask pools matched 18,194,633 original Spec records exactly across 4,600 stratified saved states, three budgets and both paid-prefix modes.
* Simplified child-cut predicates matched 230,000 sampled actual transition/spec combinations. Unavailable-mask buckets matched all 13,497 actual eligible children in a further stratified test.
* The optimized executable reproduced saved frontiers 0 through 4 byte for byte. Resuming frontier 2 reproduced frontier 3 byte for byte.

The completed checked-pool run has frontier sizes 4, 71, 1,515, 27,350, 229,477, 484,350, 162,401, 10,997, 476, 73, 11, 1, and 0 at depths 1 through 13. Frontiers 14 through 19 are also empty. It never reports a target. There are 1,072,127 interned wire functions and 628,741 factor-cut leaves. The unoptimized 2,997-pool stage through depth 6 took 842.777 seconds; the optimized resume with 3,229 checked pools took 192.735 seconds. Resuming a complete weaker-pool frontier with independently justified additional pools preserves the search coverage. Complete stdout and stderr for both stages accompany this source, along with exact counts in results.json. The later I/O hardening changes only rejection of corrupt inputs and handling of failed trace writes: repaired resume2-to3 and resume12-to19 reproduce every saved frontier byte for byte. Independent replay of all factor leaves is in progress and is not yet claimed complete in this snapshot.

The separate conditional 30-pool experiment also closed, at depth 12; its optimized resume took 117.108 seconds. It is included only as an experiment, and no conditional bound is needed by the checked-pool result.

The source streams now reject truncated wire words, origins, frontier headers and payloads before their contents are inspected. Pool input and all binary trace outputs throw on read/write failures. io-validation.json and factor-io-validation.json record the truncation and /dev/full regression cases. The source hash used for the original closure and the hardened delivery hash are both recorded in results.json.

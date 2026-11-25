# L-meta-2583 theory work

Active lease is held only by root. Work began after acquisition 2026-11-25T14:43:06Z. Earlier L-meta-2592 work is frozen.

## Exact strength

The task asks a no-larger IsReadK 1 replacement for every AO2 circuit computing any projective-plane incidence function (q >= 2, N=q^2+q+1, q+1 points on each line, unique line through two points). IsReadK 1 means every prime implicant has some joint proof tree with each input used once, not syntactic read-once of the circuit.

Existing checked L_meta_7684 builds a read-one star-cover circuit with size at most |E|+|P|+|L|-1 for every bipartite edge set E and vertex cover (P,L). All points form a cover, so the plane admits size at most N(q+2)-1. Existing checked L_meta_7639 proves |E|+N <= size+1 for any C4-free incidence circuit with a permutation matching and IsReadK 1. Projective incidence is regular with a perfect matching. Consequently the posted replacement theorem entails the exact unrestricted monotone AO2 lower bound N(q+2)-1. Conversely that exact lower bound plus L_meta_7684 proves the replacement theorem. The missing part is the unrestricted lower bound / normalization, not construction of the target circuit.

## Related checked corpus

- L_meta_7684: generic bipartite star-cover read-one construction, 51588 bytes.
- L_meta_4897: C4-free read-one edge+cover lower bound.
- L_meta_7639: square C4-free read-one edge+N lower bound with permutation matching.
- L_meta_1942: plane with read-two circuit only gives N*q <= 100*size.
- L_meta_7344: read-one repair for quadratic monotone functions with nontrivial overhead; does not give no-increase.
- R_meta_3491_1: generic C4-free bipartite normalization to two-level side-OR/product circuits is explicitly an unresolved reduction hypothesis.
- L_meta_971: explicit Heawood/Fano unrestricted monotone circuit lower 27, approximately 472KB.
- L_meta_1961 and L_meta_5162: q=3 lower bound under special AND nesting restrictions, not unrestricted.
- L_meta_4849: a least monotone C3/C4-free graph circuit can contain a dirty AND. Its 8-vertex graph is nonbipartite (5-cycle 0-4-7-1-6-0), so this does not alone refute bipartite normalization.

## Current route

Classify each gate by values at all-points/no-lines and no-points/all-lines: P=(1,0), L=(0,1), mixed=(1,1), B=(0,0). OR takes lattice join and AND lattice meet. Inputs are P/L and output B. A nonincreasing elimination of mixed or same-side AND nodes would imply a bilinear normalization; no proof yet. Main obstacle: B nodes can feed P/L nodes and affect behavior on mixed inputs, so monochromatic signatures alone do not justify bypassing them.

## Independent review

2026-11-25: independently reviewed semantics_prime_2583.lean (93 lines, compiled by semantics agent). Its incidence_prime_iff characterizes prime implicants as incident point-line pairs for arbitrary incidence relations; incidence_read_one_iff reduces joint read-one to those pairs. No forbidden syntax, valid aux namespace, allowed imports. Root notified PASSED, partial only.

## Read-one exact lower artifact

Prepared `theory_read1_lower_2583.lean` by copying checked L_meta_7639 under `L_meta_2583_aux.Optimality` (all helper theorem keywords changed to lemma), and checked degree/Hall lemmas from L_meta_3376. New incidence_matching turns the Hall injection into a permutation matching. New incidence_read1_lower proves N(q+2)-1 <= C.size under the plane assumptions and IsReadK 1. Hall.Basic cache is being restored by checker_audit; artifact is not yet compiled.

Primary-source context read 2026-11-25: https://pequalnp.com/papers/note-1 section7 explicitly distinguishes known read-once/multilinear bounds from unrestricted monotone circuits, and reports a superlinear explicit edge-function bound as open in the cited literature. This supports caution: no generic short same-size normalization is known from the cited sources. The page is contextual evidence, not a formal obstruction or proof.

2026-11-25: independently reviewed compiled reductions_2583_upper.lean. Its original prefix is mechanically equal to L_meta_7684 after import/namespace/final-lemma-name changes. The new incidence counting and upper construction are sound; large_circuit_case explicitly assumes C.size >= N(q+2)-1. Root notified PASSED for archival partial push.

## Certified lower bound, 2026-11-25

`theory_read1_lower_2583.lean` compiled successfully with Lean exit0: 106028 bytes, 2100 lines. Imports narrowed to Mathlib.Tactic, Mathlib.Combinatorics.Hall.Finite, PEqualNP.Defs. Uses finite Hall theorem rather than the stronger general version. Full diagnostics saved at `/tmp/oec/pequalnp-pilot-128/theory-read1-lower-2583-build.log`; inherited warnings only. Root notified to preserve immediately. Independent review requested from reductions agent.

At root request, prepared `assembled_2583.lean` combining certified prime-implicant characterization, upper construction, exact read1 lower, and `replacement_iff_budget`: for each plane and arbitrary C, the requested replacement exists iff N(q+2)-1 <= C.size. This is an equivalent reformulation, not the posted universal assertion. Awaiting compile slot.

`assembled_2583.lean` compiled with exit0 (3390 lines, 165269 bytes). Full diagnostics archived in assembled_2583.validation.txt. Root notified and semantics asked to independently review final equivalence/assembly.

## Conditional refutation bridge, 2026-11-25T15:00:01Z

At root request, `refutation_bridge_2583.lean` combines the certified generic read-one lower bound with the concrete PG(2,3) axioms certified by counterexample agent. Its final lemma says that any AO2 circuit of at most63 gates computing that exact incidence function refutes the posted universal statement (the negated statement is copied literally from the desk file). Lean compiled with exit0;2150lines108589bytes. This does not assert that a witness circuit exists. Full diagnostics archived in `refutation_bridge_2583.validation.txt`.

Search context: an indexed web-search response for https://gist.github.com/lizthegrey/5eed302d4552ffceda0f4b24bf47d0d1 reports earlier PG3 annealing stalled at one failing test and small C4-free graph enumeration without violations. Direct page opening failed; these external search results/counts remain UNVERIFIED. Our own boundary count is independent of that report.

## Structural search status

Checked L_meta_1501 preserves the number of dirty AND gates while putting a least circuit into TopForm; L_meta_8567 gives a no-larger least TopForm circuit from any correct AO2 circuit. A same-size normalization could therefore follow by proving that some least plane circuit has no dirty AND gates. This remains unproved. TopForm matters for counterexample search: an AND gate already below the target cannot lie below another AND gate. Simple seeds p AND (p AND OR(...)) violate this normal form; dirty same-side gates or dirty rectangles provide more relevant repeated-leaf patterns, though they currently add overhead. This finding was shared with the counterexample and reductions agents.

Independent reviews completed: semantics boundary certificate and its closed-set/Galois-closure extension. Both are sound, with the latter reducing required negative tests to closed point sets. The SAT and stochastic agents independently added read-one failure constraints, justified by the certified exact read-one lower bound.

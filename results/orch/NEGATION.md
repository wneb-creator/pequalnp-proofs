# Negation strategy

2026-11-25. The semantic and finite-boundary lemmas in lemmas/Negation.lean compiled successfully with Lean 4.36.0 (lake env lean, exit 0). Full logs: /tmp/oec/pequalnp-pilot-111/negation-lean-003.stdout and .stderr. This is a checked partial component, not the posted theorem.

For a cut at the only NOT gate, write the output as `f(x) = G(x, !h(x))`, where `h` is monotone and `G` is monotone in the extra input. If `h <= f`, replace the NOT output by true. If `f <= h`, replace it by false. Either substitution preserves the output. Constants must still be accounted for when this is turned into a circuit rewrite; the Boolean semantic lemma alone makes no gate-count claim.

For Petersen, the second comparison can be tested on the 15 edge assignments. The first can be tested on the 15 maximal independent assignments (10 of size 3 and 5 of size 4). Therefore a NOT that cannot be replaced by either constant has a witness pair: its input is true on one of those independent assignments and false on one of those edge assignments.

Concrete masks: edges = [3,6,12,24,17,33,66,132,264,528,160,640,576,320,288]; maximal independent assignments = [50,69,104,116,138,201,208,276,385,402,521,548,554,770,773]. Bit i denotes input i. Counts checked by Python exhaustive enumeration of 1024 assignments; the finite statements are now also Lean checked in lemmas/Negation.lean.

This filter applies directly to exactly one NOT, or to the last NOT only if the preceding cut signal is independently known monotone. It does not settle the remaining one-to-three-NOT cases.

Research read on 2026-11-25: https://pequalnp.com/papers/note-1 explicitly says exact values with NOT for general sparse edge functions remain unknown in its literature search. Its discussion does not supply a general no-cost negation elimination theorem. The source is context, not a proof dependency. Search found no allowed-host primary source establishing that theorem.

## Boundary-pair symmetries

A Python backtracking census found exactly 120 Petersen automorphisms and five orbits of maximal-independent-set/edge pairs, represented by (50,3), (50,6), (50,12), (116,3), (116,6), with orbit sizes 30,60,60,15,60. This is computational research, not yet a Lean theorem. Code: /tmp/oec/pequalnp-pilot-111/negation-orbits.py; complete stdout/stderr alongside it. It permits an exactly-one-NOT search to choose one of five semantic witness patterns up to graph automorphism, provided the search has justified that constant-removable negations may be excluded.

## Complementary identification obstruction

The proposed OR-first route cannot use a uniform 16-binary-gate lower bound on the nine-variable complementary restriction. For nonadjacent vertices 0 and 2, substitute x0 = !x2. With t=x2, c=x1, a=x4, b=x5, d=x3, e=x7, u=x6, r=x8, s=x9, the restricted Petersen function is exactly

`c OR a(!t OR s) OR b(!t OR r) OR d(t OR r) OR e(t OR s) OR u(r OR s)`.

The original cross terms a*d and b*e are absorbed: a*d implies !t*a OR t*d, and b*e implies !t*b OR t*e. Edges incident to c are absorbed by the c term, since x0 OR x2 is true.

Regrouping the expression as `c OR !t(a OR b) OR t(d OR e) OR r(d OR b OR u) OR s(a OR e OR u)` uses only 14 binary AND/OR gates and one NOT. The signed/free-complement cost is therefore at most 14, refuting both proposed 15-binary and 16-binary floors for this restriction. It is not a counterexample to L-meta-2592: inputs have been restricted. Python exhaustively checked all 512 assignments and separately simulated the improved 15-gate list. Code and complete logs: /tmp/oec/pequalnp-pilot-111/negation-restriction.py and .stdout/.stderr. The improved 15-physical/14-binary gate circuit is also Lean checked in lemmas/NegationRestriction.lean, with lake env lean exit 0 and empty stdout/stderr at /tmp/oec/pequalnp-pilot-111/negation-restriction-lean.stdout and .stderr.

For the adjacent pair x0=!x1, writing A={x4,x5}, B={x2,x6}, the two selector cofactors are each a six-cycle edge function OR two singleton inputs. No analogous small expression has been found yet.

## Sparse-reader caution

For a circuit with a single negated input x and an otherwise monotone suffix, some positive-x reader is necessary whenever the output is monotone and depends on x. With at most three total effective readers of x and !x, the nontrivial splits are (1 positive, 1 negative), (1 positive, 2 negative), and (2 positive, 1 negative). No no-cost elimination argument is established here: a later reader companion may depend on an earlier reader through gates shared elsewhere. Treating the reader companions as independent selector inputs is unsound without an additional normal-form proof.

## Full Petersen lift

The complementary-restriction witness does not lift directly to a 19-gate counterexample. With X=x0 independent from t=x2, its singleton c must become c(X OR t OR u). The first five-star expression gives an 18-binary-gate incomplete function; the improved four-star expression gives 17 binary gates, still missing ad and be precisely when X=t=0. Guarding those corrections with NOT(X OR t) introduces several additional gates.

An alternative exact 20-gate monotone seed, sent to the search agent, is

`X(c OR a OR b) OR c(t OR u) OR d(r OR t OR a) OR r(b OR u) OR e(s OR t OR b) OR s(a OR u)`.

Here {t,a,b,u}={x2,x4,x5,x6} is an independent set of four vertices. The other six vertices form the three matching edges (X,c), (d,r), (e,s). Negating a OR b has not yielded a checked or even simulation-verified 19-gate construction.

## Two direct OR readers do not by themselves imply impossibility

The proposed statement that two OR groups cannot supply all three Petersen neighbors is false without a gate-budget or minimality hypothesis, even for a completely monotone circuit.

Let X=x0, t=x2, d=x3, and let H be the edge function after deleting vertex 0. Put N=x1 OR x4 OR x5. Since t*d is an edge already included in H,

`F = H OR (((X OR t) AND (X OR d)) AND N)`.

Indeed `(X OR t) AND (X OR d) = X OR (t AND d)`, and the extra `(t AND d) AND N` is absorbed by H. Hence X has exactly two direct readers, both OR gates, and these groups supply all three neighbors without producing any false pair in the final output.

There is an explicit 23-gate monotone realization: H takes 16 gates using the five-vertex cover {1,3,7,8,9}; N takes two OR gates; the two OR readers, their AND, the AND with N, and the final OR add five more. This is larger than the posted bound and is not a counterexample to L-meta-2592. It shows that a useful elimination argument must charge the overhead of absorbing an existing edge or exploit minimality. In this particular construction, restricting X=0 makes the whole added branch redundant, so it is consistent with the desired stronger elimination bound.

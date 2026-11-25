# Independent research for L-meta-2583

## Meaning and available accepted components

`ReadK.IsReadK n C 1` is existential per prime implicant: some unfolded proof tree uses each variable at most once. It is not global input fanout. An incidence star-cover circuit is read-1.

Useful repository sources inspected:

- `L_meta_7639.lean`: a read-1 AO2 circuit for a C4-free bipartite graph with a perfect matching has `|E| + N ≤ size + 1`.
- `L_meta_4897.lean`: general read-1 cover extraction, with `|E| + |A| + |B| ≤ size + 1`.
- `L_meta_7684.lean`: read-1 construction from a vertex cover. The team already has a smaller checked construction extracted from L2393, so I did not duplicate this.
- `L_meta_8569.lean`: the same matching lower bound for a least AO2 circuit in TopForm with `junk = ∅`. The missing unrestricted step is elimination/charging of dirty AND gates, not the geometric matching arithmetic.
- `L_meta_2004.lean`, `L_meta_1942.lean`: generic essential-input bound `n ≤ size + 1`, and its plane instantiation. This alone gives `2N-1`, much less than the desired `N(q+2)-1`.

## New single-OR-reader invariant

`lemmas/SingleOrSparse.lean` formalizes a conditional semantic cut argument, independent of a full circuit-normalization theorem.

Suppose point input p has a single OR reader `(p OR h)`, h is independent of p, and the remaining monotone context is K. Write finite point/line sets A,B for an assignment and assume the circuit equation

`Incidence(A,B) iff K(A minus p, B, [p in A] OR h(A minus p,B)) = true`.

If p is absent, `(A,B)` is a false incidence input, but h accepts it, then A meets every line through p. Indeed each pair `{p},{l}` for an incident l makes `K(empty,{l},true)` true. Monotonicity lifts that to `K(A,B union {l},true)`. Since h remains true, the whole incidence function accepts `(A,B union {l})`; its accepted edge cannot use B because `(A,B)` was false. Thus l meets A.

By uniqueness of the line through p and any other point a, different lines through p require distinct points of A. Therefore `|A| ≥ q+1` once the regularity lemma gives q+1 lines through p.

This rules out a sibling accepted false input using at most q other points. It does not show that h is globally below the incidence function: a blocking set of q+1 or more points may meet all lines through p. In particular, the result is a restricted local obstruction, not the posted normalization theorem. A circuit-level bridge deriving the semantic context from a unique reader remains separate.

## Failed or insufficient shortcuts

- The incidence read-1 lower bound cannot be applied to arbitrary AO2 circuits; that would assume the target normalization.
- Real-rank arguments from the plane incidence matrix apply directly to arithmetic multilinear/read-1 representations, but ordinary Boolean AND gates can produce repeated variables before idempotent simplification. Their quadratic part may omit a Boolean prime implicant entirely, so rank N does not automatically force N AND gates.
- A single-read OR input need not have a sibling computing a singleton or a function already below the output. Nonlinear sibling terms may be masked by the context. The new invariant only forces such false terms to contain many points.

## Checked extensions and sharpness

`SingleOrSparse.lean` compiled with empty stdout/stderr; independent reviewer found the logic sound. `SingleOrCertificates.lean` appends two checked corollaries: if each accepted sibling input has a point certificate of size at most q, the sibling is below incidence on p=false; it suffices that the sibling depends on at most q point inputs. These assumptions do not constrain its line dependence.

The q+1 threshold cannot be strengthened merely from the semantic-cut hypotheses. Choose T avoiding p and meeting every line through p. Take h(A,B) to assert T is a subset of A and K(A,B,t) to be incidence(A,B) OR (t AND some line through p is true). Plugging p OR h into K computes incidence exactly: if h and a line through p are true, T provides an already accepted edge. Yet h accepts false input (T,empty). In a projective plane a line not through p is such a T of size q+1. This construction explains why arbitrary nonlinear siblings cannot simply be assumed below the function.

## Fano refutation interface

`FanoRefutationSuffix.lean` specializes the already checked read-1 lower bound to the order-two plane. Fin7 index i denotes nonzero binary vector i+1; incidence is dot product zero modulo two. Its line neighborhoods are `[1,3,5], [0,3,4], [2,3,6], [0,1,2], [1,4,6], [0,5,6], [2,4,5]`, matching the counterexample agent. The finite q=2 hypotheses and equality to these rows are proved by ordinary kernel `decide`.

The conditional theorem `Fano.refutes_posted_of_twenty_six` accepts an explicit Circuit, IsAO2, equality to the fourteen-input Fano function, and size at most 26. It then negates the exact posted universal normalization statement, since every read-1 replacement needs at least 27 gates. It does not assert any such circuit exists. The complete harness is the unchanged `StarEquivalencePlain.lean` followed by this suffix.

Compilation status: the complete `FanoRefutation.lean` harness passed with exit 0. Full logs are `/tmp/oec/pequalnp-pilot-104/fano-refutation-03.stdout` and `.stderr`; stdout contains only the existing base-file linter/deprecation warnings, stderr is empty. The independent geometry harness also passed with empty logs (`fano-geometry-01.*`). Root and reviewer were notified before any delivery.

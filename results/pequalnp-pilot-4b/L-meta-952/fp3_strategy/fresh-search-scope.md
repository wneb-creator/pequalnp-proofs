# L-meta-952 fresh pass

> Archive note: These are historical research-phase notes. Statements that no repository files were changed describe that phase, before this authorized archival checkpoint. Scratch paths and unpreserved search artifacts below are provenance, not archive dependencies.

The full statement for every q>=2 remains unproved and unrefuted. No repository file was changed. The finite synthesis results below are ordinary Z3 results, not Lean proofs.

## A proved mathematical bound: two gates per output

Let a family of distinct equal-size subsets L have size at least three, with pairwise intersections at most one. Suppose a fan-in-at-most-two AND/OR/NOT circuit computes OR_L for every L. There is no restriction on the number of NOT gates in the following argument. Then the circuit has at least twice as many gates as outputs. In particular this proves the requested numerical bound for projective planes of order q=2, but not for larger q.

Choose the earliest wire computing each OR_L as its representative output. These are distinct gate wires. No representative output can use another representative output, or an earlier wire computing any target clause, as a direct parent: for an OR gate this would give OR_K<=OR_L, and for an AND gate OR_L<=OR_K, forcing inclusion and hence equality of the equal-size target sets. Equality would contradict earliest choice. A NOT parent computing a positive target clause cannot negate to another positive target clause, as evaluation at zero already shows.

Assign each representative output a distinct parent gate as follows.

1. For an OR output, its two parents together are true on every singleton belonging to L. Since |L|>=3, one parent is true on at least two such singletons. Both parents are pointwise at most OR_L. The selected parent cannot serve as an OR parent for a distinct target K: its two singleton points would belong to L intersect K. Such a parent is not an input wire or an invalid false wire.

2. For an AND output L with parents h and g, at least one parent is used by no other representative AND output. Otherwise choose other AND outputs K and M using h and g respectively. Then OR_K<=h and OR_M<=g pointwise, whence

       OR_K AND OR_M <= h AND g = OR_L.

   Choose a point a in K\L and a point b in M\L. On the assignment supported by {a,b}, the left side is true and the right side false. This contradiction proves existence of a private parent. It is a gate wire because each parent is at least OR_L and hence true on at least three distinct singleton assignments. Different AND outputs choose different private parents.

3. For a NOT output, its effective parent computes NOT(OR_L). These parents are distinct for distinct L. They are gate wires because their value at zero is true and their value at all ones is false.

The three kinds of chosen parent are disjoint. A parent h of an OR output L and an AND output K would satisfy OR_K<=h<=OR_L, forcing K=L; the same representative output cannot have both gate operations. A NOT-output parent has endpoint values (true,false), whereas every OR-output parent has value false at zero and every AND-output parent has value true at all ones.

All chosen parents are non-output gate wires by the first observation. Thus there are at least m representative output gates and m distinct additional gates.

Unary, nullary, invalid-index, and duplicate-input cases do not evade the argument: a representative output computing a clause on at least three variables cannot be a constant or a copy of an earlier wire. For NOT only the effective first input is used, as in the project definitions.

The remaining difficulty for q>2 is to obtain q-1 additional private gates per output rather than one. The private parent of an AND output may be an arbitrary upper bound of the target clause, so the same argument cannot simply recurse on it.

## Finite synthesis evidence

The script small_synthesis.py imports the existing ctypes wrapper at lean_setup/meta952/synthesize.py. It constrains full Boolean truth tables, fan-in at most two, at most one NOT, and permits a true constant gate and the false out-of-range sentinel. The final runs below have no distinct-function restriction and no output-order restriction. SMT-LIB inputs and metadata are retained beside this report.

| Family | Inputs | Gate cap | Result |
|---|---:|---:|---|
| All four triples on four points | 4 | 5 | UNSAT, 0.25 s |
| Pasch: 012, 034, 135, 245 | 6 | 7 | UNSAT, 10.56 s |
| Cyclic triples: 012, 123, 234, 034, 014 | 5 | 7 | UNSAT, 0.75 s |
| All ten triples on five points | 5 | 13 | UNKNOWN, 60 s timeout |
| All five four-element subsets of five points | 5 | 8 | UNSAT, 9.01 s |
| Six cyclic consecutive triples on six points | 6 | 8 | UNSAT, 2.30 s |
| All six five-element subsets of six points | 6 | 11 | UNKNOWN, 60 s timeout |

The Pasch family is a linear hypergraph. The other completed families have pairs of blocks intersecting in more than one point and test the broader conjectured OR-family monotonization. No counterexample was found. The UNKNOWN result establishes nothing about satisfiability.

For the first four triple families, OR-only circuit upper bounds are respectively 6, 8, 8, and 14; the six-cycle family has an OR-only upper bound of nine. A three-variable OR output needs a pair helper, and the minimum pair covers give matching OR-only lower bounds. For all four-element subsets of five inputs, a prefix/suffix construction gives nine gates; the analogous construction on six inputs gives twelve gates. The finite results do not establish general size-preserving monotonization or the posted all-q theorem.

## Other theoretical observations

Writing the unique NOT input as the monotone function f and replacing its output by an independent z gives monotone cofactors F0_L and F1_L. Exact correctness implies the sharpened pointwise interval

    f AND OR_L <= F0_L <= OR_L <= F1_L <= f OR OR_L.

Neither uniform constant substitution nor replacement of the common NOT wire by a single monotone function is a general size-preserving argument. Redundant circuits can violate those local replacement properties while still computing a simple positive clause. A genuine global rewrite, or a stronger multi-level charging argument, is still needed.

There is also a useful exact cofactor invariant. Assume f(0)=0. If a wire h has actual value h(0)=1, its independent-z monotone function H satisfies H(0,1)=1, hence H(x,1)=1 for every x. Thus an AND output with a one-at-zero parent equals its other parent throughout the region f=0. If the same zero-at-zero parent is used this way by two outputs L and K, the two target clauses agree on f=0. Consequently f(e_i)=1 for every point in the symmetric difference L triangle K. For projective lines this is 2q singleton-trigger inputs of f. This is an exact semantic statement; a gate-count amortization from it has not been proved.

# Semantics and one-NOT separator analysis

## Circuit audit

`FanInTwo` restricts every gate to AND, OR or NOT and at most two input indices. `size` counts the entire gate list, including NOT, constants, copies and unused gates. Evaluation is a left fold appending one wire per gate; an unavailable index is false. There is no recursion/forward-wire loophole. The posted hypothesis permits any positive number of NOT gates, not just one, and permits dead NOTs. The expression has the intended 15 Petersen edges.

## Existing finite normalization

`lean/PEqualNP/CircuitLowerBounds/Helpers/Count.lean` gives `clamp`, `normalize_eval`, and `exists_decode`: on n inputs, a size-s circuit can be represented with exactly s gates, each input/output index bounded by n+s, padding with false gates. The finite descriptor is `List.Vector (Fin 3 × Option (Fin (n+s+1)) × Option (Fin (n+s+1))) s × Fin (n+s+1)`. These helper modules are not permitted direct imports for the current gap; needed proofs must be copied into its namespace. Normalization preserves existing NOT gates, so the positivity-of-NOT premise survives.

## One-NOT separator constraint

Write a one-NOT circuit as monotone prefix h and monotone tail G(x,y), so f(x)=G(x,¬h(x)); let G0=G(x,false), G1=G(x,true). Pointwise G0≤f≤G1. If replacing the NOT by either constant changes the output, there must be:

- an independent input S with h(S)=true (where G1 differs from f);
- an input T containing an edge with h(T)=false (where G0 differs from f).

Since h is monotone, extend S to a maximal independent set, and shrink T to one edge. Thus every essential sole-NOT input separates some maximal independent set from some edge: h(M)=true and h(e)=false. A circuit whose h implies f can replace NOT by true globally; a circuit whose f implies h can replace NOT by false globally. This is a necessary constraint, not a proof of the 19-gate bound.

The prefix/tail monotonicity and in-place replacement primitives already have proofs in `MetaComplexity/Helpers/OneNotPiece.lean`; `OneNotSplit.lean` gives the split under unique-NOT hypothesis.

## Exact finite enumeration (Python, 2026-11-25)

Petersen independent sets by size: 0:1, 1:10, 2:30, 3:30, 4:5. Maximal independent sets: ten of size 3 and five of size 4. Their bit masks (bit i is vertex i):

`50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773`.

The 15 edge masks plus these 15 maximal-false masks are the truth-table boundary. `notes/data/lrat-link/gennot.py` generates CNF in the format of the existing Lean LRAT circuit link and has a `rows` option for this boundary. UNSAT on those rows proves impossibility; SAT must be checked on all 1024 inputs when NOTs are allowed.

## Dead route

Do not claim a sole NOT is always replaceable by one constant for a monotone output. Counterexample from theory agent: majority3 = ab∨ac∨(¬a∧(a∨bc)); both constant replacements change it. Structural cancellation may still eliminate it more cheaply, but requires proof.

# Independent bounded-subset checkpoint delta review

Verdict: PASS for bounded finite-field research. This is an export policy only; saved consequences are not a certified Gröbner basis and a finite-field result does not prove characteristic-zero inconsistency.

All 21 provenance hashes and the parent provenance hash agree. The solver arithmetic, F4 hook locations, conversion implementation, and C input wrapper are byte-identical to the previously reviewed checkpoint engine. The Python runner changes only its isolated engine directory. The generator and resulting C delta were inspected directly.

The new policy copies each nonzero active row's index, nonzero term count, and leading total degree into a separate allocated array. The comparator orders this array by leading degree, then term count, then original active index. Greedy compaction writes only earlier positions of the same auxiliary array; it cannot overwrite an unvisited entry. A row is selected only when its complete term count fits the remaining budget and the existing generator-count bound. No active solver row, coefficient, hash table, basis index, or pair data is changed. All original generators are retained. The production limit is one million derived terms; the compile-time control limit is two.

Available, selected and omitted counters are exact differences of the same counted nonzero rows and terms. The original overall input bounds remain checked. In particular, the policy is not a promise that any arbitrarily large original input fits: the unchanged wrapper bounds still apply. For the reviewed full-star input, the retained original prefix has only 2,450 terms. Publication and retention logic are unchanged from the previous reviewed adapter.

Independent read-only checks covered both control suites: 108 retained snapshots preserve the exact original prefix and all 186 appended rows reduce to zero against independently computed ideals. All 42 completed or resumed bases agree with those ideals. Fifteen latest snapshots actually omit terms. For every one of the nine two-term-budget stopped runs, the selected rows exactly equal independent greedy filtering of the full-budget snapshot at the same round, and all available/omitted counts agree. This verifies real omissions rather than merely exercising a parameter.

Evidence: `check.py`, complete successful `check.log`, exact `source-diff.txt`, source hashes, and the discovered control-file inventory. No source, solver state, input, or frozen control was modified, and no heavy solver was launched for this review.

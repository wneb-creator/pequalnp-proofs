# Common-singleton obstruction in several dirty gates

This bundle does **not** refute L-meta-3754. It checks a family of nonminimum circuits for matching graphs, showing that the established local consequences of leastness do not force all dirty AND ancestors of a clean AND to share a singleton.

For the two-edge matching F = ab OR cd, use the four clauses a OR c, a OR d, b OR c, b OR d. Their conjunction computes F with seven gates. Group the first two clauses and the last two clauses: the two dirty AND outputs are a OR cd and b OR cd, with singleton supports {a} and {b}. The output is a clean AND of these two non-pure operands. A clean circuit computes F in three gates, so leastness is explicitly absent.

The script constructs prime-CNF circuits for matchings with 2 through 5 edges. Exhaustive full truth tables verify the target function, lift fixedness, all gates live and edge-critical, every AND operand not below F, and all semantic wire functions distinct. The independently written audit additionally verifies that redirecting ANY gate to either of its operands changes the computed function. OR bypasses lose an actual graph edge; AND bypasses create a false positive.

The family uses 7, 19, 43, 91 gates, compared with clean upper bounds 3, 5, 7, 9. Thus local irredundancy and edge-criticality do not imply a minimum circuit.

Reproduce from this directory with Python 3:

```
python3 multiple-dirty-probe-audit.py > repeated-audit.json 2> repeated-audit.stderr
python3 multiple-dirty-probe-independent.py
```

The audit is finite computational evidence about the named examples, not a Lean proof and not a general lower bound. The exact gap remains unresolved by this bundle.

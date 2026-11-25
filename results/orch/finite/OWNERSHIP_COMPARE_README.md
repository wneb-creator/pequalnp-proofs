Direct ownership-existence comparisons
======================================

The earlier `--require-bad-own` experiments asked whether some minimum-size
circuit has a non-owning AND. That does not refute the posted existential
statement. These experiments add `--require-all-own` and compare its lower
bound with the unrestricted upper bound at the same gate budget. A refuting
candidate would need an unrestricted SAT witness at budget K and an
all-ownership UNSAT result at that same K, followed by formal certification.

Both new scripts use the Z3 installation/version recorded in `sat_solver.json`
and the exact edge/maximal-independent-set sample set described in
`SAT_README.md`. SAT witnesses are independently evaluated on every Boolean
input, and strict AND ancestor sets are reconstructed directly to verify
every claimed owned edge. No result here is Lean-certified.

`sat_ownership_compare.py` uses the existing explicit ancestor relation.
`sat_ownership_bitset.py` instead associates to each signal the bitset of
edge inputs on which any AND in its inclusive cone is true. Inputs and free
constants start with zero. At gate j the strict cone mask is the OR of its
two operand masks. If j is AND, its inclusive mask additionally includes
its own edge-value mask; otherwise the strict mask is unchanged. Thus the
owned-edge mask is exactly `gate_value AND NOT strict_cone_mask`. This is an
exact recurrence, with no structural approximation.

All-ownership mode refuses semantic distinct-prefix pruning. Redirecting a
duplicate OR function to an earlier AND could introduce a true AND ancestor
and destroy an ownership witness. By contrast, removing unreachable gates
and topologically sorting independent gates preserves the actual cones.
OR copies pad a circuit with fewer than K gates without adding AND ancestors.

The explicit-ancestor version omits sampleconstant intermediate signals.
This normalization is valid for an at-most-K all-ownership query: replace a
sampleconstant signal by its Boolean constant and fold constant operands in
later gates. Each surviving gate keeps the same value on all edge samples,
its AND ancestors can only be removed, and the output stays correct on all
edge and maximal-independent samples. Hence its old owned edges survive.
The bitset version disables this normalization in all-ownership mode, so
its lower-bound query needs no constant-folding premise. Both scripts permit
free constants; this is a relaxation for UNSAT lower bounds. Any returned
SAT witness using the free true signal would require explicit constant
folding before interpreting its gate count in the project circuit model.
The recorded small SAT witnesses do not use free true.

Example commands from the repository root (with the unpacked Z3 wheel on
PYTHONPATH as in `SAT_README.md`):

```
python3 results/orch/finite/sat_ownership_compare.py cycle5leaf 7 --timeout 120 --ordered
python3 results/orch/finite/sat_ownership_compare.py cycle5leaf 7 --timeout 180 --ordered --require-all-own
python3 results/orch/finite/sat_ownership_compare.py cycle5leaf 8 --timeout 60 --ordered --require-all-own
python3 results/orch/finite/sat_ownership_bitset.py theta233 10 --timeout 120 --ordered --require-all-own
```

The five-cycle with one pendant leaf has six vertices, six edges, minimum
vertex cover three, and an ownership-good eight-gate construction. Both
unrestricted and all-ownership seven-gate queries are UNSAT in the stored
explicit-cone runs; an eight-gate all-ownership witness is SAT and fully
verified. The bitset query without sampleconstant pruning independently
returns UNSAT at seven gates in 4.7 seconds. Thus this graph shows no
separation. The theta(2,3,3) graph has
seven vertices, eight edges, cover number four, and an eleven-gate
construction. Both ten-gate all-ownership attempts time out: the explicit
cone run returns UNKNOWN after 180 seconds and the bitset run after 120
seconds. These UNKNOWN results provide no lower bound.

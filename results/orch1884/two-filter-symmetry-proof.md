# Checked exclusion for all ordered neighbor-filter pairs

`AllTwoFiltersOrders.impossible` extends the checked canonical two-filter exclusion to any two distinct vertices from `{1, 4, 5}`, in either temporal order, and to either operand order inside each AND filter. The statement concerns an actual circuit and does not assume semantic properties of the NOT operand.

Its explicit structural hypotheses are:

- One NOT gate separates a monotone prefix from a monotone suffix.
- Two distinguished suffix AND gates read that NOT gate and the two selected raw input vertices.
- Those raw vertices occur in no other gate inputs, in no NOT operand, and are not the output wire.
- The remaining gates contain at least two gates reading one of the two rails, raw input 0 and the free extra input 10.
- Total size is at most eighteen, and the full circuit computes the Petersen graph function on ten raw inputs plus the free complement of input 0.

The theorem proves these hypotheses impossible. It does not establish that every eighteen-gate candidate has this structural form; the global classification remains a separate task.

The proof uses six explicit graph automorphisms fixing vertex 0. For each ordered pair, the first selected vertex maps to 1 and the second to 5. Lean checked injectivity and target-function preservation, including all Boolean assignments. A generic rewiring proof fixes input 10 and every gate or invalid index at least 10, transports actual circuit evaluation, preserves sole-reader exclusions, and preserves the rail-reader count. A final commutativity proof permits reversed AND operands.

Checked sources:

| File | Lines | Bytes | SHA256 |
| --- | ---: | ---: | --- |
| TwoFilterSymmetry.lean | 133 | 5645 | cc0dd981903a8dac90ba906a781c0f79e8984b1295c5361cc97c40fcb589dd5e |
| AllTwoFilters.lean | 87 | 4215 | f0d0220f99cd6c631dc14f74b18940fe2ba1b9d2f894aa213520643d69e55fe8 |
| AllTwoFiltersOrders.lean | 51 | 2891 | bc945f14e6edb873f6c9680ffa2dea398a4409f6e43ea49726865970188bbe30 |

Each module compiled and exported successfully with exit 0. Complete logs are `/tmp/oec/pequalnp-pilot-103/1884-two-filter-sym-second.stdout/.stderr`, `1884-all-two-second.stdout/.stderr`, and `1884-all-two-orders-second.stdout/.stderr`. The first two pairs are empty; the last stdout contains one unused-simp warning. `two-filter-automorphisms.json` records the independently generated finite permutations matching the checked source.

The separate axiom query succeeded with exit 0 and reports exactly `propext`, `Classical.choice`, and `Quot.sound`. Complete logs are `1884-all-two-axioms.stdout/.stderr` in the same scratch directory. A direct format scan of these three sources found no forbidden substring, quote, admitted proof, new axiom, native decision procedure, or compile-time command.

To rebuild the entire dependency chain from committed sources, run:

```sh
bash results/orch1884/rebuild-two-filters.sh
```

This first runs `rebuild-auxiliary14.sh`, then exports eleven additional modules in the order recorded in `two-filter-dependencies.json`. It reuses the same explicit `LEAN_PATH`, module root, helper builds, and complete-log handling. The optional first argument selects the log directory; `PEQUALNP_REAL_LAKE` may select the installed Lake executable. No toolchain path from the lost container is needed.

The script and dependency graph were checked statically; the complete script was not rerun after authoring. The individual module exports were already checked. This remains a dependency-module result requiring the permitted single-file packaging before a posted-theorem submission.

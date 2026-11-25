# Local star-cut resynthesis

This is computational solver evidence for restricted circuit families, not a Lean lower-bound proof. For each of42 choices of two vertices from one bipartition, complementary stars and their OR aggregate are frozen as the prefix. SAT synthesizes an arbitrary tail using all original inputs and every frozen intermediate, with total24 gates. It allows AND, OR, NOT and the free false wire. Initial constraints contain all552 negative assignments and19 edge minterms; any SAT model is evaluated on all16,384 inputs and counterexamples added.

The unrestricted initial local queries have18 UNSAT and24 timeouts. Normalized retries add sound output-cone and actual-fanin-order symmetry breaking, independently audited. The aggregate.json records their final combined coverage; a timeout is not UNSAT. Both a phased25-gate control and normalized fixed25-gate control pass full evaluation.

Complete finished solver logs, command arguments, scopes, samples, decoder schemas and results are retained. Heavy CNF files remain in scratch and their SHA256 hashes are recorded; source regenerates them. The source, original model and normalization were independently reviewed. No counterexample has been found.

Additional blocked queries use all six necessary single-reader conditions proved in ../lemmas/BlockingAll.lean (SHA25668527669db4674208e15e8768ae5abf788ff79cb35273142b3efdec9c6d3cc6a). The original clause generator and compact reader-disjunction compression were independently reviewed against the Lean statements; captured review messages and exact source hashes accompany them. These cuts are necessary for full target correctness, even though each SAT query initially samples571 assignments. Both cut versions pass25-gate positive controls on all16,384 inputs. The compact helper is also supplied to the global SAT agent.

Source retains the original scratch sibling-directory names star-cut and small-one-not. Restore those names when reproducing the saved relative imports; repository artifact directories use underscores.

Bounded local runs are finished: 41 of the42 frozen-prefix pair families are excluded by solver UNSAT, and one remains unresolved after90 seconds with the blocking cuts. A three-star/9-variable-gate-tail query remains UNKNOWN after separate120-second default,180-second UNSAT-profile and120-second blocked runs. No result here excludes arbitrary24-gate circuits.

reader_capacity.py supplies a separately audited redundant cut for FULL variable circuit schemas only: with all14 inputs and all nonoutput gates read, D+F≤S+1−14, where D counts inputs with at least two distinct reader gates and F counts selected false-sentinel slots. It must not be applied unchanged to these frozen-prefix models. The global SAT agent received this helper; its implementation, independent audit and integration reviews are preserved here.

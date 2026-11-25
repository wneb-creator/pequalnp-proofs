# L-meta-3754 finite circuit searches

This is a computational audit, not a proof or refutation of the posted statement. SAT controls are checked on every Boolean assignment. UNSAT means Z3 reported UNSAT for the saved finite query; no kernel-checkable UNSAT certificate was produced. UNKNOWN means the time limit expired and supplies no exclusion. No optimal-size dirty circuit has been found in this checkpoint.

## Encoding

The basis is constant-free, two-input AND/OR with earlier-wire references. Every gate is in the final output cone. Samples contain all graph edges as two-point inputs and every maximal independent set. Monotonicity makes agreement with the graph edge function on these samples equivalent to full agreement. A wire is BelowF exactly when it is false on all maximal independent-set samples. Every real AO wire is satisfiable at the all-ones input. Consequently lift fixed point is exactly the rule that each OR has two operands with matching BelowF status. Dirty queries require an AND whose output is not BelowF.

Adjacent independent gates are ordered lexicographically by operation and parent indices. The lexicographically least topological ordering satisfies this: swapping an inverted adjacent independent pair lowers the first differing key; later wire renumbering cannot undo that decrease.

Separate strengthened query sources encode necessary properties of a globally minimum circuit:

* `minimal`: a gate has neither a constant sampled truth vector nor the same sampled vector as an earlier wire. Redirecting a duplicate or propagating a sampled constant would otherwise give a smaller AO circuit agreeing on all extremal samples, and hence computing the same full function. Constant propagation needs no constant gate because the final sampled output is nonconstant.
* `minimal-clean`: additionally, AND operands may not be BelowF. Bypassing an AND to a clean operand preserves zero output on false graph inputs and can only increase the output elsewhere, hence keeps the target function.
* `critical`: additionally, forcing any gate to false must destroy acceptance of some edge input. Otherwise constant propagation removes that gate while preserving every positive minimum and all false inputs.
* `critical-auto`: additionally, the first gate's input pair is the least pair in its graph-automorphism orbit. Choose the lexicographically least circuit over graph automorphisms and topological orders to justify this symmetry. No operation restriction is added.

These are ordinary mathematical coverage arguments, not formal Lean normalization certificates. A SAT model satisfying the strengthened conditions still need not be minimum: the P4 five-gate dirty control demonstrates this. The metadata value `standard_bound` is the star-cover construction size |E|+tau-1, not an automatically established lower bound. In particular theta333 size12 SAT, if found later, would require a separate minimum proof. The unrestricted theta333 size11 query permits repeated/idempotent gates and so includes all smaller circuits by padding; it has no dirty or fixedpoint requirement.

## Reproduction

The exact saved SMT2 files are authoritative query inputs. The Python programs use Z3 5.3.3, installed for this job under the scratch path encoded near their start. Supply graph JSON, gate count, timeout in milliseconds, and mode to the generic scripts; the original `dirty-optimum-synth.py` instead takes path/cycle and a vertex count. Adjust scratch/output paths to rerun elsewhere. No downloaded solver binary or package is included.

Each SAT result is separately evaluated on all 2^n assignments, with graph coloring/C4-freeness, full output truth table, BelowF flags, dirty-AND status, fixedpoint, and full gate ancestry checked. Critical queries additionally test the edge witness for every forced-false gate. Full stdout and stderr are retained in each log.

## Completed queries

| Query | Result | Seconds |
| --- | --- | ---: |
| cycle6-size8-control-critical-auto | SAT | 0.006 |
| cycle6-size8-control | SAT | 0.002 |
| cycle6-size8-dirty-minimal | UNSAT | 18.461 |
| cycle6-size8-dirty | UNSAT | 25.087 |
| cycle8-size11-dirty-minimal-clean | UNKNOWN | 180.018 |
| cycle8-size11-dirty | UNKNOWN | 180.133 |
| cycleleaf7-size9-dirty-minimal | UNKNOWN | 30.01 |
| doublestar6-size6-dirty-minimal | UNSAT | 0.602 |
| path4-size4-dirty | UNSAT | 0.01 |
| path4-size5-dirty-critical-auto | SAT | 0.13 |
| path4-size5-dirty-critical | SAT | 0.16 |
| path4-size5-dirty | SAT | 0.182 |
| path5-size5-dirty | UNSAT | 0.06 |
| theta3338-size11-unfixed | UNKNOWN | 180.05 |
| theta3338-size12-dirty-minimal-clean | UNKNOWN | 180.09 |
| theta3338-size12-dirty | UNKNOWN | 180.015 |
| threefork7-size8-dirty-minimal | UNSAT | 20.954 |

Checkpoint created 2026-11-25T17:25:58.132243+00:00. Active searches were excluded from this checkpoint.

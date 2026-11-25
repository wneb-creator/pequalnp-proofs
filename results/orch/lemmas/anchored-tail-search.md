# Anchored AND–OR tail search

Prepared 2026-11-25 08:52 UTC. This is a finite sufficient construction family, not a lower bound or a successful 26-gate synthesis.

Let `G` be the posted Heawood edge function, `F0` its 18-edge restriction obtained by deleting vertex 13, and `A = x1 OR x2 OR x4`. The earlier relaxed co-output proposal sought a 24-gate circuit on the other 13 inputs computing `F0` and `W` with `A <= W <= A OR F0`. Appending `x13 AND W` and an OR with `F0` would give 26 gates. That proposal has not been searched.

The new family permits a 24-gate prefix on all 14 original inputs, with three arbitrary prefix wires `C,U,V`, followed by exactly two gates:

```
T = U AND V
output = C OR T
```

Require `C` on the 18 minimal true rows of `F0`, and require the final output on the 21 minimal true and 37 maximal false Heawood rows. Monotonicity makes these constraints sufficient on all 16,384 inputs. They imply `F0 <= C <= G`: the core anchors give the first inequality, and `C <= output = G` gives the second. No extra constraints are imposed on `U,V`. This includes the relaxed co-output proposal by setting `C=F0`, `U=x13`, `V=W`, while also allowing `C` to include additional valid contributions and allowing both factors to be computed signals.

The known 27-gate baseline computes the six right stars of `F0` in 23 gates, computes `A` with two OR gates, and appends the two-gate tail. Three 26-gate seeds instead compute only two of `x1,x2,x4` in one OR gate. Each seed computes exactly `G` minus one of `(1,13)`, `(2,13)`, `(4,13)`. Every seed still computes exact `F0` at `C`, satisfies all core anchors and all negative output rows, and has exactly 47 false negatives on the full truth table. All four artifacts were exhaustively checked on 16,384 inputs each.

The source is `/tmp/oec/pequalnp-pilot-70/constructive/anchored_tail.py`. It calls the separately reviewed `circuit-search/repair_base.py` with no canonical prefix, no liveness, no minimality, no dirty-gate or quadratic-shadow condition, and repeated initial operands permitted. It then adds lexicographic normalization only between adjacent gates within the prefix. It deliberately does not compare the final prefix gate with the appended AND: that AND may use early wires while `C` is computed late, so a global ordering condition could exclude even the known baseline. No graph-automorphism normalization is imposed because fixing vertex 13 is not invariant under the full group.

The 26-gate instance has 7,249 variables, 199,034 clauses and 58 rows. The fixed 27-gate baseline smoke returned SAT in 0.198563 wall seconds / 0.127925 CPU seconds. The decoder checked every CNF clause, selected operands, all encoded row outputs, the fixed tail, `F0 <= C <= G`, and all 16,384 full assignments. No target-budget solver was launched by this agent.

Stable artifacts in the constructive scratch directory:

- `anchored_tail.py`: generator, fixed-witness smoke preparation, and full verifier.
- `anchored-tail26.cnf` / `.map.json` and generation log: unsearched target instance.
- `anchored-tail-baseline27.json`: exact baseline.
- `anchored-tail-seed26-missing-1-13.json`, `-2-13.json`, `-4-13.json`: exact one-edge-missing seeds.
- `anchored-tail27-smoke.cnf` / `.map.json`, `-solve.log`, `-run.json`, `-verified.json`, `-verify.log`: fixed baseline smoke and complete verification.
- The `*-base.cnf` / `.map.json` files record the unmodified base encoding before the tail additions; CNFs need not be committed if disk cost is undesirable, because the source and command metadata reproduce them exactly.

An UNSAT result would concern only this anchored AND–OR architecture. The 18-edge anchor and final two-gate shape have not been proved necessary for arbitrary 26-gate circuits.

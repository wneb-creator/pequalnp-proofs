P10 residual-mask finite checks

Scope: accepted Heawood input labeling, ineligible points {0,1,2,3}; eligible points {4,5,6} and all seven lines. Local line t means actual input 7+t. This is finite research and helper certification, not a proof of the posted gap.

The four neighborhood rows are {0,1,3}, {0,2,6}, {1,5,6}, {0,4,5}. A nonempty residual mask at an adjacent line x forces line t into the point's assigned operand whenever r(x) is a subset of r(t). The assigned-consumption inequalities allow 2+card(r(t)) slots. One additional slot is needed for an eligible adjacent point, except at line7 (local0).

Two units: independent set-based Python and bit-based C++ enumerate all16,384 assignments and find zero. The 508-line Lean certificate checks the same Boolean table by 64 ordinary-kernel blocks and assembles an arbitrary-code-function theorem. Its SHA256 is f8ee44cc4553c657cc979a577b0f6c6ba5984456e5c1c71099103bc4d68d7e92. The successful -j1 -M6000 build exited0. An earlier -M3000 build exited134 with an interpreter memory exception; all logs are retained. Algebraic independently reviewed the source and independently enumerated the same finite obstruction. Lean_setup supplies the separately reviewed Finset bridge; root owns actual-circuit transfer.

Three units: the weak bound leaves155,222/2,097,152 assignments. The deterministic gzip contains the full surviving weak census. Refinement uses only existing rules under explicit full/protected-mask hypotheses: forbidden missing masks, known full-mask sharing, protected three-slot exactness, iterative residual co-label closure, assigned consumption and the free-eligible cofactor bound. No optional two-slot exactness rule is used. Four saturated Bplus13/Bzero1 patterns retain2826,2826,2988,2826 assignments. These assignments are necessary-condition survivors, not actual circuits. The JSON records complete counts and up to20 examples at each cofactor stage.

Reproduction from repository root:

```sh
python3 results/orch/lemmas/stochastic-p10-minimal-constraints.py /tmp/oec/pequalnp-pilot-81/p10-two-recheck.json
g++ -O3 -std=c++17 results/orch/lemmas/stochastic-p10-residual-enum.cpp -o /tmp/oec/pequalnp-pilot-81/p10-enum
/tmp/oec/pequalnp-pilot-81/p10-enum 3 /tmp/oec/pequalnp-pilot-81/p10-three-recheck.json
python3 results/orch/lemmas/stochastic-p10-three-unit-refinement.py results/orch/lemmas/stochastic-p10-pattern-input.json results/orch/lemmas/stochastic-p10-residual-three.json.gz /tmp/oec/pequalnp-pilot-81/p10-refined-recheck.json
```

The older stronger two-unit experiment is preserved as exploration, including an explicitly optional unproved two-slot rule. The final two-unit certificate does not rely on any full/protected mask, missing-mask, cofactor, or optional two-slot rule.

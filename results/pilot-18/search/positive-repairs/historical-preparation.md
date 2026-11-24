# All-positive near-circuit repair preparation

No solver or annealing worker was launched for this work. Main controls resources.

The existing reviewed engine and wrapper accept `--weight 16` unchanged. The
energy is `16*FN + FP + 0.02*live`, where FN counts the 16 positive edge rows and
FP counts the 24 maximal-independent rows. An all-positive state with at most
15 FP has lower energy than every state with a missed edge. This is a preference,
not a constraint: all-positive states with 16 or more FP may lose, and only strict
overall best states are saved. Runtime effectiveness has not been established.
`positive-weight16-source-analysis.json` binds the executable, wrapper, seed pack,
and a proposed unlaunched 60-second command for coordinator scheduling.

## Actual existing sources

The 15 saved best states from seeds134218..134221 were independently evaluated
on all2048 inputs. Three already accept all target-positive inputs. The useful
two are `stochastic-candidate-134218/engine-result.json.best-3.json` and
`engine-result.json.best-4.json`. Both compute exactly `F_G OR x9`, have five
false-positive boundary rows and22 false-positive inputs, and have a junk AND at
gate14. The first has21live gates; the second has20live gates, with gate12 dead.
These are incomplete sources, not witnesses. Their scalar evidence is in
`prior-best-positive-intake.json` and `positive-real-families-review.json`.

There are only four prepared real-seed formulas:

- `positive-best3-family/distance-k03.cnf`
- `positive-best4-family/distance-k03.cnf`
- `positive-best3-family/negative-free05.cnf`
- `positive-best4-family/negative-free05.cnf`

After main's independent review, the two K3 cases are the suggested first small
pilot, at10–20seconds each with one worker. The local5 cases are optional next
alternatives. Do not scale all families solely because earlier runs were UNKNOWN.

## Generator and exact semantics

`prepare_positive_repairs.py SOURCE FRESH_DIRECTORY` accepts strict acyclic
21-gate augmented circuits (ordinary inputs0..10, FALSE11, TRUE12, gate13+g).
It sorts commutative operands and independently recomputes all2048 source values.
Production intake requires all positive inputs accepted and1..15 false-positive
boundary rows by default. Exact sources are rejected from repair intake so they
can go directly to independent candidate/Lean verification.

The generator reuses hash-pinned reviewed helpers. Every formula keeps the exact
target's full40 boundary constraints. It removes the original forced-first-junk
unit and the source-output pin. No clean-prefix, liveness, first-junk, second-junk,
or tail shape is imposed. Constants and repeated operands remain available.
Output selection is free and does not count against the gate edit budget.

Distance mode uses the existing exact keep flags and signed totalizer to allow
at most K changed gate descriptions. Local mode fixes all gates outside a chosen
set; the chosen set ranks forced-FALSE effects by FP corrected versus accepted
edge rows lost. This ranking is only a heuristic. All clauses still require the
exact target, including every positive row. These are numbered local
neighborhoods, not complete coverage of all size21 circuits.

For source analysis without generating CNFs:

```sh
python3 -B /tmp/oec/pequalnp-pilot-18/orch/S02/prepare_positive_repairs.py \
  /tmp/oec/pequalnp-pilot-18/stochastic-candidate-134218/engine-result.json.best-3.json \
  /tmp/oec/pequalnp-pilot-18/orch/S02/fresh-positive-analysis --analysis-only
```

For a two-case fresh family:

```sh
python3 -B /tmp/oec/pequalnp-pilot-18/orch/S02/prepare_positive_repairs.py \
  /tmp/oec/pequalnp-pilot-18/stochastic-candidate-134218/engine-result.json.best-3.json \
  /tmp/oec/pequalnp-pilot-18/orch/S02/fresh-positive-family \
  --budgets 3 --local-counts 5
```

## Controls and limits

`audit_positive_repairs.py` checks14 deterministic all-positive superfunctions
obtained by replacing one AND of a known22 circuit with an operand. These are
explicitly wrong synthetic controls. It performs30,720 scalar input checks,
840 suppression checks, four exact CNF reconstructions, two complete synthetic
known22 model validations, rejection checks, and11 byte-identical reproduced
files. The known22 models repair an OR back to AND and change the deliberately
wrong TRUE output to the target; the full validator confirms every clause and
all2048 inputs but correctly reports that the21-gate limit is not met.

The real four-case family has four additional exact CNF reconstructions. Reviews
bind source and artifact hashes. Full audit/validator stdout and stderr are kept;
the final audit exits0 with empty stderr. Earlier control passes remain preserved.

Any future SAT model must pass the full CNF/model validator, normalization and
all2048 checks, then the posted Lean proof pipeline. UNKNOWN and uncertified local
UNSAT are not global or assigned-shard refutations. No exact21 witness exists in
this handoff.

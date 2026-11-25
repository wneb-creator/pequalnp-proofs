# Five sole-essential-NOT cases

Prepared for L-meta-2592; no SMT search has been launched from this directory.

The checked orbit certificate uses these mask pairs, with bit i equal to input xi:

| Case | Maximal independent mask M | Edge mask e |
| --- | --- | --- |
| 0 | 50 | 3 |
| 1 | 50 | 6 |
| 2 | 50 | 12 |
| 3 | 116 | 3 |
| 4 | 116 | 6 |

The certificate's permutation p sends M to its representative and sends the edge to its representative. Relabeling inputs gives h'(x)=h(x composed with p), so h'(representative M)=true and h'(representative e)=false. The library agent confirmed these conventions and that its frozen Lean certificate compiled.

`search.py --case k` models 19 gates with exactly one NOT. It requires that NOT's operand to be true on M and false on e. The recommended `--essential-at-pair` flag additionally requires forcing the NOT output to true to produce true at M, and forcing it to false to produce false at e. These stronger constraints are simultaneously valid: forced circuits are monotone, so an essential negative witness can be extended to a maximal independent set and an essential positive witness shrunk to an edge, preserving the corresponding error. The library agent reviewed this argument.

The default allows binary identity gates (equal predecessors), so a smaller clean circuit can be padded to 19 gates. `--strict-binary` excludes that padding and is an optional heuristic restriction. `--normalize-not` optionally moves the sole NOT immediately after its operand producer, or first when its operand is a raw input. Neither optional restriction is enabled by default.

Other search normalizations: valid backward references, no constant gates, output last, every nonoutput gate live, and canonical ordering of adjacent independent equal-operation gates. Constants/invalid reads and dead gates require cleaning; any UNSAT result here remains a solver result, not a Lean proof or a completed normalization theorem.

## One allocated solver slot

Choose exactly one case per allocated slot. For example:

    python3 /tmp/oec/pequalnp-pilot-109/counterexample/five_cases/search.py --case 0 --essential-at-pair --budget-seconds 600 --output /tmp/oec/pequalnp-pilot-109/counterexample/five_cases/case-0-witness.json > /tmp/oec/pequalnp-pilot-109/counterexample/five_cases/case-0.log 2>&1

Substitute case numbers 1 through 4 and distinct output/log names for the remaining cases. The default starts with 30 boundary assignments and adds independently discovered counterexamples. `--rows 91`, `--rows dense`, or `--rows full` select stronger initial samples. The wall budget covers the entire CEGIS loop, rather than restarting on each solver check.

Every SAT model is evaluated independently on all 1024 inputs. A witness file is written only after the full truth table, gate count, backward references, and NOT count have been verified. It is explicitly labeled as Python-verified, not Lean-checked. No statement-false result should be reported as machine-checked before Lean checks the concrete circuit.

## Dead or inessential NOTs

The five essential cases do not settle dead or inessential NOTs. Those require a separate monotone circuit of size at most18 case, after deleting the dead NOT or replacing an inessential NOT by a constant and folding constants. The size-preserving/decreasing normalization is a separate proof obligation.

The same program prepares that search:

    python3 /tmp/oec/pequalnp-pilot-109/counterexample/five_cases/search.py --monotone18 --budget-seconds 600 --output /tmp/oec/pequalnp-pilot-109/counterexample/five_cases/monotone18-witness.json > /tmp/oec/pequalnp-pilot-109/counterexample/five_cases/monotone18.log 2>&1

A verified monotone18 candidate is converted into a 19-gate counterexample by appending a dead NOT and retaining the old output wire, then independently rechecking all1024 inputs.

Preparation validation: Python syntax compilation and all six static `--dry-run` modes passed. Dry runs validate the masks and initial sample counts and do not import Z3 or call a solver. Actual SMT encoding has not been executed yet.

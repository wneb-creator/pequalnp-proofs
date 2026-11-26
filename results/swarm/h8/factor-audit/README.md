# Independent factor-leaf audit

All 628,741 retained factor cuts from the full monotone Petersen search passed
independent Python replay. The audit checks complete binary framing, hashes,
every wire's expression and 1,024-bit truth table, exact input identities,
distinct nonconstant live functions, absence of the target, all 225 proper
positive/negative separation pairs, and the Horn/parity/cross obstruction.

This is an audit of factor leaves. It does not establish frontier completeness,
other pruning rules, circuit normalization, a Lean certificate, or the posted gap.

`summary.json` records the completed original audit. `baseline-level7.stdout`
and `remaining.stdout`, with their empty stderr files, are its complete logs.
The two original wire DAGs were also checked to have identical common prefixes.
The checked run's complete factor trace was verified to equal the frozen
level-7 prefix concatenated with the level-8-and-later suffix.

`replay.py` is a portable wrapper around the independently implemented
`factor_cut.py`; it uses the final, larger DAG for all three snapshots.
`snapshots.json` fixes all hashes, record counts and budgets. Run it with normal
Python 3 (not `python -O`):

```sh
python3 replay.py --wire-file /path/to/wires.bin \
  --factor-dir /path/to/frozen --out-dir /tmp/factor-replay \
  > /tmp/factor-replay.stdout 2> /tmp/factor-replay.stderr
```

The large binary inputs are not committed. Their original task locations are:

* Final DAG: `/tmp/oec/pnp-swarm-2373-8/fullprobe/compact-stronger/wires.bin`.
* Factor directory: `/tmp/oec/pnp-swarm-2373-8/fullprobe/audit/frozen/`, containing
  `baseline-level6.bin`, `checked-level7.bin`, and `checked-level8plus.bin`.

These local task paths may be unavailable in another checkout. Obtain the
retained traces or reproduce the native searches described in
`../full-monotone/README.md`; the hash checks intentionally refuse different
data. This package makes no network requests and does not generate the traces.

The portable wrapper was additionally exercised on the first 100 actual frozen
leaves with the complete final DAG. The full original replay used the same
factor logic and independent strict binary parsing; the portable wrapper's full
628,741-record replay has not been repeated merely for packaging.

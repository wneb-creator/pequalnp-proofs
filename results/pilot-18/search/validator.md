# SAT witness validation for L-meta-1342

Run from an explicit working directory with Python 3; no dependencies, solver,
network access, or Lean invocation are needed:

```sh
python3 /tmp/oec/pequalnp-pilot-18/lean-setup/validate_sat_candidate.py /absolute/path/instance.cnf /absolute/path/kissat.stdout
```

The metadata must be `/absolute/path/instance.json`. Exit 0 means the signed
model, every CNF clause, requested circuit constraints, and both original and
normalized truth tables passed. Exit 1 prints `REJECTED:` to stderr. An UNSAT
or UNKNOWN result is rejected; this utility does not validate proof certificates
or establish search completeness.

After successful validation it writes these files beside the CNF:

- `instance.validated.original.json`: decoded augmented circuit, actual junk
  indices, requested-constraint audit, and input hashes.
- `instance.validated.normalized.json`: real inputs 0 through 10, gate wires
  `11 + g`, gates, output, size, normalization counts, and input hashes.
- `instance.validated.json`: audit summary and absolute artifact paths.

The metadata SHA-256 must match the complete CNF bytes. Separate metadata and
Kissat stdout SHA-256 hashes bind the saved result to the audited input snapshots.
The model must explicitly assign every declared variable, with no contradictory
signs, and have a SATISFIABLE status and final zero terminator. Consistent repeated
literals are accepted and counted. The complete DIMACS stream is checked, including
literal bounds, header/count agreement, and the last clause.

The decoder requires exactly one source in each selector array and exactly one
output. It evaluates all 2,048 assignments of the fixed eleven-input graph.
Virtual false/true inputs, Boolean identities, and aliases are folded; dead gates
are pruned and the remaining gates are renumbered. The normalized circuit must
again compute the target on all 2,048 inputs, contain no dead gates or constants,
and use no more gates than the original. Constant-output fixtures are supported
by the normalization helper, but cannot pass the nonconstant target check.

Constraint handling:

- `enforce_junk` defaults to true. When true and `first_junk >= 0`, the first junk
  AND must occur at that index; `second_junk` additionally requires another junk
  AND. `enforce_junk=false` skips those suffix requirements, as needed by tail7.
- Whenever `first_junk >= 0`, every earlier AND must be false on **every** negative
  target input, independently of `enforce_junk` and other flags.
- `prefix_sort`, `prefix_lex`, `prefix_distinct`, and `productive_prefix` check
  source ordering, AND-first lexicographic ordering, distinct descriptions,
  and nonempty singleton support for both operands of every prefix AND.
- `prefix_dominance` requires each prefix AND to have an exact minimal-edge input
  where it is true and each earlier clean prefix gate wire is false. Cleanliness
  of that earlier wire is tested on every negative input. The report counts
  audited gate/wire pairs. Inputs and virtual constants are not predecessor gate
  wires in this constraint, matching the generator's range over earlier gates.
- `prefix_copy_chain` recognizes structural `OR(w,w)` copies. Any such copy at
  gate `g > 0` must read wire `13 + g - 1`; every subsequent prefix gate must also
  be an OR copy of its immediate predecessor. A copy at gate zero may read any
  available source. The report counts copies checked.
- `live`, `last_output`, `last_op`, and `suffix_shape` are checked when requested.
  Prefix flags require a nonnegative boundary. Flags must be JSON Booleans.
- `tail_template` is covered by the complete CNF audit rather than a separate
  template decoder.

`meets_posted_gate_limit` reports whether the normalized size is at most 21.
The valid 22-gate control intentionally passes this utility with that field false.
Every report has `lean_checked=false`: success is a witness audit, not acceptance
by the repository's Lean checker. Revalidate after changing any input file.

Validation evidence is recorded in `validator-validation.json`; full test stdout
and stderr are retained in `validator-tests.stdout.txt` and
`validator-tests.stderr.txt`. The suite includes the verified-v2 fixed-cover22
model (4,800 variables, 99,415 clauses, normalization 22 gates to 22 gates),
constant/alias fixtures, a 41-gate target-preserving fixture normalized to 22 gates,
and malformed-model/CNF/constraint rejection cases. It performs no solver runs.

```sh
python3 /tmp/oec/pequalnp-pilot-18/lean-setup/test_validate_sat_candidate.py
```

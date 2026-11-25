# Phase hints with optional LRAT output

This is a scratch-built wrapper for the official CaDiCaL 3.1.0 C++ API.
The original wrapper is included for comparison and was not modified.

`cadical-phase-lrat [--default|--sat|--unsat] [-t seconds] input.cnf
[--phase-file signed-literals.txt] [--lrat-file new-proof-path]`

The new option sets `lrat=1` and `binary=0`, then starts `trace_proof`
before `read_dimacs`; this preserves initial preprocessing steps. After
solve, it calls `conclude` and `close_proof_trace`. UNKNOWN or SAT output is
explicitly identified as not an UNSAT certificate. A parse-time timeout
closes the trace and marks it incomplete. Existing proof paths are refused.
Phase preferences remain `Solver::phase` calls after loading; no clauses or
assumptions are added by a hint.

Build completed with exit 0 and an empty complete log. Command:

```
g++ -std=c++17 -O2 -I /tmp/oec/pequalnp-pilot-85/sat-tool/cadical-rel-3.1.0/src /tmp/oec/pequalnp-pilot-85/sat-tool/cadical-phase-lrat.cpp /tmp/oec/pequalnp-pilot-85/sat-tool/cadical-rel-3.1.0/build/libcadical.a -lpthread -o /tmp/oec/pequalnp-pilot-85/sat-tool/cadical-phase-lrat
```

All tiny controls passed; complete stdout/stderr/command/exit records are
under controls/. The SAT control forces variable 1 true while its supplied
phase prefers false, demonstrating that a phase is not an assumption. The
UNSAT trace is `3 0 1 2 0`, which is direct unit propagation from `[1]` and
`[-1]`. It maps to the already kernel-checked repository-checker tokens
`[2,0,0,2,1]` in KernelLRATSmoke.tiny_unsat. The zero-time control reports
UNKNOWN, and attempting to overwrite the existing UNSAT trace exits 1
without changing its hash.

Independent diff/API review by the counterexample agent passed for source
SHA256 483193583107e3c94ce00515795aa35827f735a385d110f10f949f51d83815fe.
The agent checked CONFIGURING-state trace setup, absence of added constraints,
conclude-state requirements, trace closing/incomplete reporting, and refusal
to overwrite an existing path. The exact-25-gate full-formula control also passed: SAT exit 10 in
3.0127 seconds, with independent validation of all 1,575,093 CNF clauses
and all 16,384 input assignments, zero mismatches. Its complete 29.7 MB
stdout/stderr is preserved losslessly as official25-control/control.log.gz;
metadata records the uncompressed digest and a checked compression roundtrip.
The authorized 300-second target run is coordinated separately by that agent.

No target SAT or UNSAT result is asserted by this wrapper archive. Binary
hash and control metadata are recorded in metadata.json; the executable is
reproducible from the source and pinned public CaDiCaL release.

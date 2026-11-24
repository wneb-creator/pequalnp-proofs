# L-meta-1342, shard 17: reproducible search checkpoint

This is unfinished search work on the fork branch. It is not a proof submission.
The adjacent Lean file proves the target edge function with 22 gates; the posted
bound is at most 21. No proof or refutation of that bound has been obtained.

Run `python search_l1342_shard17.py OUTPUT_DIRECTORY` with Python 3 to regenerate
all seven DIMACS inputs. The program uses only the standard library and makes
no network requests. Its SHA256 and all seven CNF hashes are in reproducibility.json.
Kissat 4.0.4 is searching the cases with `--unsat --time=7200` and binary DRAT
proof output. A result requires a separate SAT model or UNSAT certificate check.

The seven cases conservatively cover the assigned FIRSTJ=17/two-junk range.
They are deliberately broader after formula normalization: tail junk flags
are no longer required. Repeated leaves and free constants remain allowed.
The mathematical reductions and encoding reviews are included. They are not
Lean formalizations. Exhausting this range would not refute the global statement.
The current cost variant uses the reviewed distinct-prefix restriction.

Reviewer scratch paths identify the files actually examined. The combined
program here contains those components and reproduces the running CNFs exactly.
No lease identifiers or authentication data are included.

Sub-agents: 2 inherited-model agents for mathematical search and independent validation/proof engineering

The dominance and copy-chain variants add independently reviewed restrictions.
Invoke either script with `--distinct-prefix OUTPUT_DIRECTORY` to reproduce its
seven cases. The environment restarted at approximately 01:36 UTC, interrupting all old
solver processes without a verdict. Their incomplete traces are not certificates.

`validate_sat_candidate.py INSTANCE.cnf KISSAT.stdout` checks the complete model,
every clause, both full truth tables, and constant/alias elimination. Its report
separately says whether the normalized circuit meets the 21-gate limit.

The streaming certificate checker is the unchanged default-width C build from
https://github.com/ccodel/dsr-trim (read 2026-11-24). Source blob hashes, build
logs, and positive/negative controls are included. It must return the explicit
UNSAT verdict; exit zero with `s VALID` does not establish unsatisfiability.
No assigned-shard certificate has yet been checked.

The cost variant adds the reviewed proper-support lower bound when a prefix
wire covers all graph edges. Free TRUE remains exempt. Run
`python search_l1342_shard17_cost.py --distinct-prefix OUTPUT_DIRECTORY`.
Both mathematical and encoding reviews passed; the seven new cases are running
or queued. No SAT/UNSAT verdict has been obtained.

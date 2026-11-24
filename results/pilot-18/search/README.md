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

The ancestor-cost variant additionally removes absorbed noncopy OR gates and
bounds every prefix wire using its residual accepted edge graph and exact
structural ancestor cone. Mathematical and separate encoding reviews passed.
Run `python search_l1342_shard17_ancestorcost.py --distinct-prefix OUTPUT_DIRECTORY`.
All seven CNF hashes are in ancestorcost-reproducibility.json. Two strong cases
are running with online checkers; all four weaker solver states are paused.

The included online runner forwards binary DRAT through a bounded FIFO to the
unchanged hash-pinned DSR checker. It retains full logs and a proof hash, but
no replayable certificate. It accepts only the explicit solver/checker UNSAT
verdicts with successful exits and a complete producer stream. Fifteen controls
passed, and the runner received an independent source review. No production
case has yet produced a verdict.

The constant-canonicalization and exact-counter variants received independent
source, clause-delta, and mathematical review. Reproduce the newest inputs with
`python search_l1342_shard17_ancestorreverse.py --distinct-prefix FRESH_PARENT`,
then `python add_suffix_some_junk.py FRESH_PARENT FRESH_OUTPUT`. The separate
postprocessor requires at least one suffix junk AND, a consequence of the
22-gate clean lower bound. It does not restore the original gate-17 or two-junk
requirements after rewriting. All seven output hashes are bound in the reviews.
The exact counters add 10,325 clauses and no variables; canonical constants add
17 clauses, and the suffix consequence adds one. Runtime benefit is unmeasured.

A 1,200-second candidate-only run on the previous ancestor encoding returned
UNKNOWN. Its complete stdout/stderr are preserved. Short candidate runs now
cover the seven new shapes; the two original online-checking runs continue.
Neither campaign has established SAT or UNSAT for an assigned case.

The newest source postprocessors expose two further reviewed restrictions.
`add_ancestor_support.py PARENT FRESH_ALL_SEVEN` adds the necessary consequence
that a prefix gate whose singleton support has no common neighbor can only
have OR descendants, all retaining its support. Its assumptions include clean
productive prefix ANDs and exact structural ancestry. Independent review checked
all seven parent semantics and clause deltas; exhaustive helper tests and 1,024
random clean prefixes passed. It adds 204 variables and 3,536 clauses per case.

`add_common_and_antichain.py PARENT FRESH_THREE` keeps proper supports of common
outer-AND factors pairwise incomparable, allowing full-support factors. Only
meet5, meet3or2 and meet2or1meet2 are constrained. Main independently reviewed
the source and reconstructed every appended clause on original and combined
parents. The latter three cases now run candidate-only searches with bundled
CaDiCaL 2.1.2. Tiny SAT/UNSAT controls passed; no production verdict is claimed.
Complete hashes for all seven support cases and three combined cases are in
combined-cuts-reproducibility.json. Reproduction order is the reverse generator,
one-junk postprocessor, ancestor-support postprocessor, then optional antichain.

The reviewed original-DAG variant retains the arbitrary four-gate suffix and
the original gate-17/two-junk requirements. It appends the ancestor-support
consequence and six clauses requiring at least three suffix AND gates. The
latest junk gate must reach a later clean AND before the false output; the
original liveness premise provides that path. No fixed-tail rewrite is used.
Reproduce with `python build_original_strong.py PARENT/prefix-distinct.cnf FRESH`.
The builder pins both its parent CNF/generator and its support-helper source.
Its CNF has 11,968 variables and 114,566 clauses; its hash and independent
completeness/delta review are preserved. One verified UNSAT for this original
DAG would exclude the assigned shard under the reviewed normalizations, without
requiring seven template results. It would not refute the global Lean statement.
A CaDiCaL --unsat run now streams its certificate through the unchanged checker
runner. No production verdict has been obtained.

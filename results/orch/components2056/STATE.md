Component synthesis handoff, 2026-11-25 18:49 UTC

Active query: V3 target63, original unrenamed grammar. Native PID34114,
tool session63932. Started18:06:47.275 UTC with native wall limit3600s,
expected finish about19:06:47. It was SIGSTOP/SIGCONT paused for48.391516s
during publication recovery; it was never restarted and its native timer was
not reset. Full logs/metadata are v3-target63-run.*; pause record is
v3-target63-pause.json. No verdict as of the handoff time.

Parent alone owns lease renewals, git, and publication. Do not launch another
long worker without fresh parent authorization/renewal. The V3 learned state
must remain unchanged through its scheduled run.

Prepared, fully independently reviewed successor: V5 grammar with output
reachability and equivalent baseline64 polarity warming. It has6616 profiles,
146124 productions,876540 variables and2674606 clauses. Original target CNF
SHA7236084a40c0266039b696a65c2984d93d27736ba5ef6e05d1a0050e0bd72594;
warm target SHA41e93ad00666f64bf01ffa406004afd76bc62c6ce37f76f93c02218df857fd2e.
The baseline64 assignment violates exactly the expected64th-selection budget
overflow. Positive64 native/inverse models and756-row semantic replay pass.

Use run_sat_warm_checked_v2.py (SHA6436498c5abcfe9060a6b182e0598cb050cd3020921ade2f5917925ba4132d04),
which verifies both CNF signs, unrenames the model, decodes the circuit, and
forwards/reaps cancellation for every subprocess. Native and postprocessor
SIGTERM controls passed. component-warm-final-review.json contains the full
independent approval and evidence hashes.

The following is a prepared invocation, not a launch authorization:

    python3 results/orch/components2056/run_sat_warm_checked_v2.py \
      --cnf /tmp/oec/pequalnp-pilot-121/components2056/v5-target63-warm.cnf \
      --original-cnf /tmp/oec/pequalnp-pilot-121/components2056/v5-target63.cnf \
      --mapping results/orch/components2056/v5-target63.mapping.json \
      --library results/orch/components2056/v5-library.json \
      --phase results/orch/components2056/v5-target63-warm.phase.json \
      --prefix results/orch/components2056/v5-target63-warm-run \
      --seconds 3600

Separate reviewed successor option owned by proof_route: V5 plus a necessary
nonread1-edge cut at bound<=63. Scratch v5-nonread-target63.cnf has896388 vars,
3984136 clauses, SHA42dc7c44a6d99d6cea4acfd67754e30b0e2454f8d69b19b84bf77b04f8307565.
The actual67-gate positive control satisfies all4374259 clauses and756 rows,
with3 edges lacking joint read1 proofs; the pinned64 read1 control is UNSAT.
This file is unrenamed. Existing warm_phase.py must NOT be applied unchanged
to its extended mapping; a separately reviewed phase extension is required.

Raw CNFs stay scratch and are deterministically regenerable from archived
sources/data. preparation-identity.json, preparation-v5-identity.json, and
preparation-warm-identity.json bind omitted files and their commands. Full
models for controls are archived compressed. No63-gate witness or unrestricted
lower-bound claim has been obtained.

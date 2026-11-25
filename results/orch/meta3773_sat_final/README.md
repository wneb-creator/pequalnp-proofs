# Final restricted SAT attempts

No 63-gate witness or global refutation is claimed. These are incomplete
diagnostics, not new Lean proofs.

The original six-point round 1 fixes all seven outside OR trees to variant 0
and exactly seven AND gates. It returned unknown after 110.02 seconds. Its
scope is only that tree configuration.

The denser six-point model uses 17 raw inputs, 13 compatible outside OR
signals, 76 extremal rows, and a 28-gate local budget. Its 25-gate matched
overapproximation accepts all 24 positive edges and incorrectly accepts 26
maximal negative cuts. Padding by an absorbed valid edge and two OR gates,
then colex ordering, was checked to preserve its function on all 131,072
physical assignments. The bounded repair permits at most eight gate changes
and leaves all compatible outside-tree choices free. It retains the reviewed
active-gate, positive-gate, bad-AND and helper-count restrictions.

The dense 29-gate positive control passes every one of its 298,062 original
and polarity-renamed clauses. Its decoded function passes exhaustive physical
verification. That control has 29 local gates and is not a 28-gate witness.
The warm wrapper only renames variable polarities and always checks the
original clauses after inverse model decoding, then all 131,072 physical
inputs. Production statuses and full solver logs give each actual outcome.

This small delta preserves complete sources, exact inputs, metadata and all
stdout/stderr. The large final DIMACS files are not duplicated: CNF_BINDINGS
records their exact hashes and lengths. They regenerate deterministically
using the frozen source snapshots and exact input files. The old six-point
input is already in ../meta3773_sat_six; all dense inputs are in this folder.
With files restored under /tmp/oec/pequalnp-pilot-79, the generation commands are:

    python /tmp/oec/pequalnp-pilot-79/meta3773-six-sat-r1-source.py --round 1 --gates 28 --and-count 7 --fixed-trees --generate-only
    python /tmp/oec/pequalnp-pilot-79/meta3773-six-dense-repair-r0-source.py --round 0 --near-seed /tmp/oec/pequalnp-pilot-79/meta3773-six-dense-matched-over-seed.json --changes 8 --generate-only
    python /tmp/oec/pequalnp-pilot-79/meta3773_dense_phase_run.py --stem meta3773-six-dense-repair-r0 --run 0 --generate-only

All invocations run from the repository or named job directory. The wrappers
bind source/data/CNF hashes and apply ordinary child environments, disabled
core dumps, and CPU/address-space/wall limits. Any actual witness still needs
assembly and checking on the original 26-input instance and prescribed head.

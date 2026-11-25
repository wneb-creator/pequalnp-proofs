# L-meta-2583 structure survey and Fano search

Owner: not_elimination. Parent owns the lease and all git/desk actions.

## Exact meaning and obstruction

The target asks that every AO2 circuit for a projective-plane incidence
function can be replaced without increasing size by a circuit with
ReadK.IsReadK at k=1. The ReadK definition tracks whole vectors of leaf
multiplicities in proof trees, with OR union and AND capped vector addition.
Thus it does not have a scalar-count loophole. TopForm.IsAO2 requires every
gate to be an AND or OR of exactly two earlier wires.

The existing star construction has N*(q+2)-1 gates. Existing checked lower
bounds for read1 circuits give that same lower bound when the incidence graph
has a perfect matching and no 4-cycle. Consequently the posted target would
give a sharp unrestricted monotone circuit lower bound, rather than merely
the weaker asymptotic lower bounds already checked for read2/read3 circuits.

## Existing checked components

- L_meta_7684: AO2 read1 star construction from any bipartite vertex cover,
  size at most |E|+|A|+|B|-1.
- L_meta_4897: C4-free bipartite graph and read1 circuit imply a cover with
  |E|+|A|+|B| <= size+1.
- L_meta_7639: the perfect-matching specialization gives |E|+N <= size+1.
- L_meta_2237 and L_meta_6369: analogous simple-graph/read1 cover statements.
- L_meta_6579: syntactic separated point/line OR support at every AND implies
  ReadK at k=1.
- L_meta_1942 and L_meta_2058: projective-plane read2 lower bounds with large
  constant losses (100 and 112).
- L_meta_2581: projective-plane read3 asymptotic lower bound.

The more general C4-free read1 replacement is open as L-meta-4895. Its three
reduction files R_meta_4895_1, R_meta_4895_215, R_meta_4895_628 retain either
the unrestricted sharp cover-budget bound or the unrestricted matching-charge
bound as a hypothesis. They do not resolve the missing lower bound.

## Counterexample search assigned by parent

Use the order-two cyclic plane with point/line labels 0..6 and incidence
(p-l) mod 7 in {0,1,3}; inputs are point0..6 and line7..13. A 26-gate AO2
circuit would refute the target, since the read1 lower bound is 27.

The 21 minimal true assignments and 37 maximal false assignments are a complete
test set for monotone circuits. circuit_search independently generated those
58 rows and verified the 27-gate star seed on all 16384 inputs. Data lives at
/tmp/oec/pequalnp-pilot-121/fano-sat/fano-data.json.

My one-CPU C++ search is
/tmp/oec/pequalnp-pilot-121/not-elimination/fano_local.cpp,
with complete logs fano-local.stdout and fano-local.stderr in that directory.
The initial bounded run has seed2583 and a 1200-second wall-time budget.
It randomizes either point or line star constructions and their OR trees,
deletes one gate, then uses annealing, multiple simultaneous rewires, whole-gate
mutations, safe gate permutations, fanout redirection, and a pool of near hits.
All proposals are validated to read only earlier wires. Evaluation uses all
58 extremal rows in a single uint64 word. A zero-error candidate requires an
independent exhaustive check on all 16384 rows before any proof work.

Initial progress: one missed minimal true edge and no false positives, which
is the expected star-minus-edge plateau and is not evidence of a counterexample.

## Search stopped on an existing exact lower bound

The first search ran 447.6 seconds and logged 2,216,763,154 proposals, with one
missed edge as its best result. A second objective required the canonical
incident edge (point0,line7) to be accepted without a joint read1 proof tree,
and penalized semantically duplicate intermediate wires. Its complete logs are
fano-dirty.stdout/.stderr; it ran about29 seconds and46.8million proposals.

Both searches were terminated immediately after gate_elimination discovered,
and circuit_search independently verified, a hidden unrestricted exact lower
bound in L_meta_7997: heawood_lb_27, fano27 and ao27 at lines9341--9429 prove
27 <= size for every AO2 circuit computing this cyclic Fano function. The
file's final theorem has a reread hypothesis but its proof does not use it.
Thus a 26-gate Fano counterexample is impossible. No search process remains.

## Checked finite search certificate

results/orch/lemmas/FanoCriticalRows.lean compiled successfully with exit0.
Independent review approved SHA256
b8beaa68ec15633bbc3cba1d5fa50a4dc9e3c4af7e743a64a11c028849229851.
Its theorem correct_of_critical_rows proves that agreement on the listed21
positive and37 negative masks suffices for any monotone Boolean function.
The proof uses a kernel check over128 point-subset closures, and independent
review reproduced the full finite data. Complete compiler output is stored in
not-elimination/fano-critical.stdout/.stderr (both empty).

The first certificate attempt was terminated before success because bounded
existential quantification over BitVec14 enumerated all16384 masks instead of
only the37 listed masks, reaching9.35GiB memory. The successful version uses
List.any/List.all and a BitVec7 representation of the point subset, so only the
intended finite cases are evaluated. Parent was notified immediately to push
the compiled partial under the push-early rule.

## Order-three Singer plane

Parent next assigned a bounded20-minute, one-CPU search for a63-gate circuit
on26 inputs with incidence (p-l) mod13 in {0,1,3,9}; the known star upper
bound has64 gates. A survey of15 checked files containing64-gate bounds found
only structural hypotheses (productive ANDs, line-degree1, no nested ANDs,
or a single nested pair), not an unrestricted bound.

circuit_search generated52 minimal true masks and704 maximal false masks,
and status_review independently reproduced and compared the exact756-row set.
The data are plane3-sat/plane3-data.json. My verifier
not-elimination/verify_singer.cpp also checked the64-gate positive control on
all67,108,864 assignments using64-bit parallel evaluation; its output is
singer-control.stdout, with no stderr.

The stochastic engine singer_local.cpp uses12 uint64 blocks per wire and
three-bit joint-read1 flags on canonical edge(point0,line0), inputs0 and13.
Its objective encourages that edge to be accepted without a joint(1,1)
witness. Fano-specific single-variable-read restrictions are not assumed.
The initial seed258313 run began after the parent's15:03:19UTC renewal.

## Generic checked correctness certificate

IncidenceCriticalRows.lean compiled exit0 with empty diagnostics. Independent
review approved SHA256
8cc4f28ad5823dbd5a8d372d2b49f8c5b2582777aafe521c71b80129c5d38a7f.
For an arbitrary finite bipartite incidence relation, it proves that a monotone
function is correct when it accepts all incident-pair inputs and rejects all
point-subset closure inputs. A second theorem allows any listed negative test
family covering those closure inputs. There is no finite enumeration or
lower-bound hypothesis in this helper. Parent was notified immediately on
successful compilation for the push-early rule.

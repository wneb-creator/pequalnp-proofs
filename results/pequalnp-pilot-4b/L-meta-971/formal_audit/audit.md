L-meta-971 audit and first synthesis result

The exact posted statement elaborates unchanged under PEqualNP.Defs in Statement.lean. The command exited0 and statement.log reports only propext for the proposition definition. This is well-formedness, not a proof.

Monotone2 requires only AND/OR gate operations and fanin at most two. The existing append-only evaluator permits constants from empty gates, unary gates, repeated inputs, and unavailable reads defaulting to false. No semantic loophole was found. The target is the exact edge-existence function of the listed21-edge graph on14 inputs.

lean_setup independently enumerated all16384 assignments:458 independent sets,37 maximal independent sets. The21 edge-pair positives plus37 maximal-independent negatives are a complete test family for monotone circuits. Every positive input contains an edge; every independent input extends to a maximal independent set. The ordinary27-gate star construction was verified on all16384 assignments.

The encoder cadical_synth.py gives every gate a freely selected AND/OR operation and two one-hot-selected earlier inputs. It allows both free constants, repeated operands, duplicate functions, and unused gates. It uses only commutative operand ordering and makes the unique output the last gate. The model covers a smaller circuit by discarding gates after its output and padding before the last gate. Constants can be propagated away from a SAT candidate. No target arbitrary-circuit-to-CNF completeness bridge has been checked in Lean.

lean_setup independently inspected the encoder, validator, and normalization and found no issue. The explicit27-gate fixture model satisfies all176395 generated clauses, and both its free-constant interpretation and normalized original-index circuit agree on all16384 assignments. The fixture-test.log command exited0.

First full26 query:58 complete samples,6032 SAT variables,165574 clauses. CaDiCaL ran with a180-second time limit and1536MiB address-space cap. It returned UNKNOWN, exit0, after180.114 seconds; maximum resident set size103.45MB. No SAT model or UNSAT verdict was produced. Full26 CNF2612682 bytes, partial LRAT804359173 bytes, and full solver stdout/stderr25692 bytes are retained under full26.*. The partial trace is not an UNSAT certificate.

Any subsequent SAT model is evaluated on all16384 assignments before being accepted as a counterexample. The numerical source cap and kernel certificate bridge obstacles from previous gaps still apply to an eventual UNSAT proof. No repository file was modified by this agent.

Final synthesis ledger

All four searches ended UNKNOWN with exit0 after the stated time cap. None returned a SAT model or an UNSAT verdict. No solver remains running from this agent.

| Prefix | Scope/options | Time cap | Driver elapsed | Max RSS |
|---|---|---:|---:|---:|
| full26 | Complete58-row encoding, default solver |180s|180.114s|103.45MB|
| satphase26 | Same encoding, --sat --phase=false |180s|180.210s|146.60MB|
| first-or-01 | Same samples, first gate fixed OR(0,1) |90s|90.180s|93.21MB|
| canonical26 | Same samples, ordered largest source indices and all gates used |180s|180.253s|90.70MB|

All used a1536MiB address-space cap. The first two have165574 clauses; the fixed-prefix query has165577; the canonical query has175699. Every query has6032 variables. Full CNFs, instance metadata, complete stdout/stderr, partial LRAT traces, and result JSON remain on disk. search-ledger.json records exact sizes and times. The four incomplete traces total about5.56GB; none is an UNSAT certificate.

The first-OR fixed query is a discovery restriction, not a complete lower-bound test alone. Python-verified Heawood automorphisms from lean_setup give the expected three unordered input-pair orbits; no complete Lean symmetry/circuit-renaming bridge was constructed here.

The canonical layout has an independently reviewed paper completeness argument. Prune gates outside the single output cone, sort the remainder by syntactic depth and then by largest renamed operand index within each depth. The largest operand index is globally nondecreasing. The live output is last. Any smaller circuit can be padded by repeated-input copy gates after the output, preserving this ordering and ensuring every gate has a later reader. This differs from the earlier multiple-output task, where such useful-padding completeness was not automatic. A Lean proof of this normalization is still absent. The depth-sorted27-gate positive fixture satisfies all187341 canonical test clauses and all16384 assignments.

Independent mathematical audits also found no flaw in literature_route safe-branch lifting or the unique singleton context fact for a monotone gate with two singleton supports in a loopless C4-free graph. fp3_strategy SafeMeetCounterexample correctly refutes a stronger cumulative partition potential using P5; it does not refute Heawood27. prior_routes RunTrim and ThreePayment lemmas are sound within their explicitly stated free-AND Run model; they do not yet prove the actual circuit lower bound.

The posted theorem remains unproved and unrefuted. The named proof file was not created by this agent; no target build, target local checker, commit, push, or PR was performed by this agent.

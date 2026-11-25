Prepared exact free-neighbor-OR searches; no target solver run.

The active L-meta-1884 lease expired before either targeted run began. Both prepared target results are PREPARED_NOT_RUN, not UNKNOWN or UNSAT. No solver process remains active. All four completed pinned diagnostic streams and wrapper streams are preserved in full.

The cofactor has nine inputs0..8 and twelve Petersen-minus0 edges, listed in free_or_cnf.py. Source9 is the specified free OR of neighbors of the deleted vertex: pair{0,3} or triple{0,3,4}. Paid gate outputs begin at10. Operator0 is AND; operator1 is OR. All operands are strict earlier wires. The exact24 extremal rows are the twelve graph edges and twelve maximal independent sets. Because every source function and every paid gate is monotone in the nine underlying variables, agreement on these rows implies exact cofactor equality; every returned candidate is nevertheless checked on all512 assignments.

Pair target:15 paid gates plus freeOR(0,3). A witness would yield a19-gate ordinary Petersen circuit after computing the helper, adding the third neighbor, ANDing with deleted vertex0 and ORing with the cofactor. It would be an improved upper bound, not a refutation of the current18-gate gap.

Triple target:14 paid gates plus freeOR(0,3,4). A witness would yield an18-gate ordinary Petersen circuit: two helper OR gates, fourteen paid cofactor gates, one deleted-vertex star AND, and one final OR. The code also shifts internal indices for the posted eleven-input list, leaving the extra free complement unused. Both lift forms are independently evaluated on all1024 rows before a candidate is accepted.

Validation: baseline16-with-free-source.json is the independently known exact16-gate cofactor circuit, with internal indices shifted by one to make room for source9. It ignores the optional source, so these diagnostic runs omit require-helper. Both free-source variants compiled to SAT under all other pruning switches, decoded correctly and passed512 rows; their20-gate lifts passed1024 ordinary and1024 posted-input rows. wrong-baseline16.json changes the final OR to AND; both pinned encodings were UNSAT. preparation-validation.json records all four results. fixture-validation.json records complete lifted fixtures and wrong-fixture disagreement sets.

Target pruning and scope: every raw input is required to be used, justified by an exhaustively found pair of assignments with identical other source values but different target values; these witnesses are recorded in each result. Internal gates must be used and the output is last. Optional productive, fresh, and primary-minimal restrictions choose a minimum circuit on the complete extremal specification. Freshness is valid for these tight targets using the existing cofactor16 floor: the free pair costs one ordinary OR and the free triple costs two, so a smaller paid circuit would contradict that floor. The source does not supply a Lean formalization of these normalization claims. No global UNSAT or new machine-checked lower bound is claimed by this archive.

Prepared commands (run only with an active authorized lease):

python3 free_or_cnf.py --free 0,3 --gates 15 --seconds 120 --tag pair15 --productive --primary-minimal --fresh --require-helper
python3 free_or_cnf.py --free 0,3,4 --gates 14 --seconds 120 --tag triple14 --productive --primary-minimal --fresh --require-helper

CNFs are reconstructible from the source and result arguments; their exact hashes and sizes are recorded in prepared-*-result.json. Large CNFs remain in scratch, rather than the branch. The source and full diagnostics are preserved here.

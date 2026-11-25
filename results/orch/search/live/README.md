Circuit search experiments for L-meta-2373

These are computational research aids, not a Lean proof or an exhaustive verdict. No full Petersen search completed and no circuit below 20 gates was found. All reported exclusions remain conditional on their stated search semantics and still need kernel certificates.

live_search_allcuts_fast.cpp is an earlier ordinary Live-state search: 1,145 cofactor profiles, Petersen automorphisms, sparse read-once closure for deficit zero, and a first-sharing-wire check for deficit one. Compile with g++ -O3 -std=c++20. Run a bounded case, for example --first andedge --seconds 30 --nodes 2000000; add --signed --cap 18 for the free-complementation mode. Other first cases are andnonedge, oredge, ornonedge, diffedge, diffnonedge. It uses only minimal-positive row columns; signed pruning can be strengthened by exact_cover.py. It does not yet serialize a complete Lean certificate.

live_search.py is the earlier Python search and common truth-table/automorphism module. formula_sparse.py and one_share.py implement closure checks; their old batch CLI expects an unarchived frontier-depth7.json sample, while their functions work on supplied root tuples. one_share.py defaults to the six archived cofactor survivors.

copy_search.py explores the experimental general first-sharing recurrence using root multiplicities. Replacing a read-once subformula on s leaves by two copies costs s-1 gates and reduces the sharing deficit by one. A general kernel decomposition remains unfinished. copy_search_irredundant.py additionally excludes outputs equal to an operand; this relies on preserving the actual Live freshness invariant through the decomposition. Both stop explicitly on time, node, or closure limits and never report a completed bound in that case.

The 30-second copy-search trials stopped earlier at a 3,000-entry closure cap after only 22 states. The saved cap state has 18 roots, all original input functions, budget 19, and no computed prefix. This is a performance limit, not evidence for or against the posted statement.

exact_cover.py finds an explicit positive/negative assignment pair that the live root pool cannot distinguish (signed mode), or violates the needed monotone separation (monotone mode). Its report confirms every first binary gate must retain both distinct input operands, for representative edge and nonedge pairs and all four normalized operations. The six archived deep frontier states pass this stronger test.

Earlier experimental lexicographic gate-order variants are intentionally omitted. Combining that ordering with graph symmetry was not justified, and no result from those experiments is used here.

The Python copies use relative paths to the adjacent cofactor archive. The archived CPP contains its finite profile tables directly and uses no network or subprocesses. Logs are complete outputs of their bounded runs.

Latest ordinary search: live_search_full.cpp adds all-positive signed dependency checks, fresh δ0/δ1 closure, all120 graph symmetries, the independently reviewed input-prefix prefilter, a separate compact restricted-value dictionary, and lazy cofactor caches. Its approximate memory stopping estimate is not a hard RSS ceiling. The --selftest option reconstructs an independent20-gate witness and checks all21 live states in both modes; all10 applicable δ0/δ1 terminal checks passed in each mode. Default runs still remain bounded experiments.

The six delta1-tables/state-*.json files hold indexed-label finite data for the six archived surviving frontier states. They include shared truth tables,225 oriented row pairs, Cert0, each two-copy Cert2, and bridge indices. Independent review checked37,466 fresh/disjoint/admissible pair-operation cases and950 bridges. export_delta1.py regenerates them; check_delta1_bridge.py is a separate compressed-multiplicity regression. Kernel instantiation is handled in separate Lean artifacts. These data do not exhaust the full target.

copy_search_pruned.py and copy_search_pruned.cpp add conditional subtree cofactor cuts to the general first-sharing experiment. The Python60-second run examined1747 states without exhaustion. The C++ implementation is an earlier performance prototype; it stopped on signature guards and does not yet incorporate the later lazy-storage/symmetry changes. The general reordering lemma remains unproved, so this route is not a certified bound.

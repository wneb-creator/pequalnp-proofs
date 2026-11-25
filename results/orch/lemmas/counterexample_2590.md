# L-meta-2590 computational route

Lease and submission belong only to root. New lease issued2026-11-25T15:07:28Z; long run authorized after renewal15:12:16Z.

Monotone2 permits only AND/OR gates with at most two inputs, including nullary gates and invalid/forward references. We therefore use the full normalized `Defs.LratEncoding.enc2` formula, whose checked L5050 completeness theorem handles those semantics and normalization. sat_encoding is adapting that theorem; no extra symmetry or visibility clauses are added to the baseline.

Independent exhaustive enumeration finds76 independent Petersen vertex sets,15 maximal independent sets, and15 minimal positive edge masks. The30 sorted rows are stored explicitly in metadata. Correctness on them suffices for monotone functions, and every SAT witness is also checked on all1024 inputs.

The20-gate known circuit was reordered by a greedy lexicographic topological order, then validated on all1024 inputs. The fully fixed enc2 positive control returned SAT, its decoded circuit passed all1024 rows, and its actual saved model satisfies all155636 CNF clauses.

The19-gate normalized baseline has138019 clauses and max DIMACS variable166533. Its SHA256 is c34d684c7fd7ee2a38a0e3f205639b7be8fe762771a72781ffca28c84810f96d. `encode.py` SHA256 is6c96af4eb803b7d58646eb55e4987b3f2f177a4da556e535dd02979fa89e7369. Full section offsets and metadata are frozen; a separate unrestricted encM has37863 clauses.

At15:12UTC a1200-second CaDiCaL run started on the exact baseline, writing binary LRAT and complete stdout/stderr. No result yet. Any UNSAT result will require verified LRAT replay against the original formula; the current files are not an UNSAT certificate.

Scratch: `/tmp/oec/pequalnp-pilot-99/gap2590/counterexample/`. Frozen inputs/control manifest: `frozen-manifest.json`. No target Lean file or Git state is modified by this agent.


## Bounded code-model obstruction,15:17UTC

The proposed abstract all-eligible code constraints alone are satisfiable. Let A={2,4,5,6}, an independent set; B={0,1,3,7,8,9} induces the matching(0,1),(3,8),(7,9). Give every A vertex a common position0 and a unique private position; every B vertex receives common position1 and a private position. Pair0 with1, pair B private positions along those three matching edges, and pair A private positions with empty positions.

With opposite p xor1, the explicit codes are W0={1,2},W1={1,3},W2={0,8},W3={1,4},W4={0,10},W5={0,12},W6={0,14},W7={1,6},W8={1,5},W9={1,7}. There are12 nonempty positions,20 memberships,8 pair IDs. Every code is nonempty, has size≤2, and contains no opposite pair. Every Petersen edge has opposite-position witnesses. Because each vertex has a private position, no code is covered by the union of any two other codes, even without restricting those two labels to a nonedge.

This is NOT a circuit counterexample. It permits12 false-positive pairs, which the proposed abstraction expressly allowed. It shows that additional temporal/circuit structure is necessary. `code_model.py` checks every stated finite condition and writes the exact model.

The suggested two-C5 slot construction was also exhaustively checked: among945 slot perfect matchings,295 obey the no-opposites-inside-a-code rule, and the maximum Petersen edge coverage is11 of15. Full source and best models are in `code_cycles.py/.json`; this finite family is impossible but the general code abstraction is not.

At15:21:53UTC the lease again returned410, confirmed by root at15:22:26. Exact enc2 solver was stopped with SIGINT at15:22:34UTC, exit130, after roughly10minutes. No SAT/UNSAT verdict. Full stdout/stderr and LRAT prefix remain preserved; this is not a completed certificate. The small AND-skeleton controls passed, but no free7–10-gate probes were launched. Final sources/logs are frozen in final-manifest.json.

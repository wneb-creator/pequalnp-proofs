# L-meta-2590 computational route

Lease and submission belong only to root. New lease issued2026-11-25T15:07:28Z; long run authorized after renewal15:12:16Z.

Monotone2 permits only AND/OR gates with at most two inputs, including nullary gates and invalid/forward references. We therefore use the full normalized `Defs.LratEncoding.enc2` formula, whose checked L5050 completeness theorem handles those semantics and normalization. sat_encoding is adapting that theorem; no extra symmetry or visibility clauses are added to the baseline.

Independent exhaustive enumeration finds76 independent Petersen vertex sets,15 maximal independent sets, and15 minimal positive edge masks. The30 sorted rows are stored explicitly in metadata. Correctness on them suffices for monotone functions, and every SAT witness is also checked on all1024 inputs.

The20-gate known circuit was reordered by a greedy lexicographic topological order, then validated on all1024 inputs. The fully fixed enc2 positive control returned SAT, its decoded circuit passed all1024 rows, and its actual saved model satisfies all155636 CNF clauses.

The19-gate normalized baseline has138019 clauses and max DIMACS variable166533. Its SHA256 is c34d684c7fd7ee2a38a0e3f205639b7be8fe762771a72781ffca28c84810f96d. `encode.py` SHA256 is6c96af4eb803b7d58646eb55e4987b3f2f177a4da556e535dd02979fa89e7369. Full section offsets and metadata are frozen; a separate unrestricted encM has37863 clauses.

At15:12UTC a1200-second CaDiCaL run started on the exact baseline, writing binary LRAT and complete stdout/stderr. No result yet. Any UNSAT result will require verified LRAT replay against the original formula; the current files are not an UNSAT certificate.

Scratch: `/tmp/oec/pequalnp-pilot-99/gap2590/counterexample/`. Frozen inputs/control manifest: `frozen-manifest.json`. No target Lean file or Git state is modified by this agent.

First-input-pair automorphism symmetry

Flag: --first-input-orbit. Off by default. Valid in both exact and at-most modes. Explicitly refuses more than6line vertices before expensive enumeration.
Backup core_sat_before_first_input_orbit.py; diff core-sat-first-input-orbit.diff.
SourceSHA85052b974b15013629aabef9b268397d8891061813a5711b8372b449b9e9118b.

Automorphisms

Enumerate all permutations of the line vertices. Partition point vertices by their exact line-neighbor subsets. Keep a line permutation iff each transformed neighbor class has the same cardinality as the source class. Map point rank i in each source class to point rank i in its target class; map lines by the selected line permutation. Every resulting map is explicitly checked to be a bijection of all n input indices and to preserve the complete exact edge set. This same-rank choice gives a subgroup (composition preserves ranks), even when additional within-class symmetries exist. Using a subgroup is sufficient.

Original core: exactly12 automorphisms, bytewise set comparison against root's independent root-core-input-automorphism-audit.json PASS. Group closure and identity independently checked. All136 sorted input pairs including repetitions split into31 orbits (25nonduplicate and6duplicate orbits). Added105 clauses reject each nonminimal first pair. No op literal occurs in these clauses: BOTH AND and OR first gates are constrained identically, with no assumption the first gate is AND.

Completeness and compatibility

The first gate can read only raw inputs. Relabeling all inputs by a graph automorphism preserves the target function and circuit size. Among all such relabelings and topological serializations, choose a lexicographically least sequence of gate keys(op,a,b). Its first rawinputpair must be minimal in its input orbit; otherwise relabeling yields a smaller first key. The same choice satisfies the existing adjacent-independent-gate ordering, since swapping an inverted independent pair yields a smaller serialization. Gate functions, essentiality, pair activity, op-specific domains, and global bypass-output witnesses all transfer under input relabeling and topological renumbering.

For canonical pins, relabel the canonical circuit under every allowed input automorphism, greedily serialize each by available gate key, and choose the lexicographically least resulting sequence. The greedy sequences satisfy adjacent-independent ordering; minimum across the group ensures the first-pair orbit condition. The final pinned circuit is exhaustively truth-checked as usual. Input automorphisms of the core need not extend to the whole projective plane: they preserve the core function in its original labels, which is all the existing full-plane extension uses.

Validation (audit_first_input_orbit.py, first-input-orbit-audit.log/json)

- Default exact and previous all-flags ordered/critical-output CNF, JSON, printed summaries byte-identical with flag absent.
- Canonical24-in25 and stripped21-in22 SAT with every existing flag plus first-orbit. Independent full-clause checks409883/258211; exhaustive truth checks65536/8192. All48/42 actual counterfactual output witnesses rechecked.
- Both control automorphism groups have12 members. Every permutation, exact edge-set preservation, group closure/id, and first-pair minimality checked independently. Original group equals root's independently derived set exactly.
- Flag alone exact canonical24 SAT with fulltruth decoder check. >6line input rejected.
- Duplicate neighborhood classes, unequal class cardinalities, and isolated points tested by brute-force comparison with all color-preserving input bijections; generated subgroup is valid in all cases.

Ready target variants (no solver launched by this task):
q3core23-first-orbit.cnf/.json: all flags including counterfactual outputs,12729variables356325clauses.
q3core23-first-orbit-domains.cnf/.json: op-domain variant without counterfactual output copies,7623variables138653clauses.

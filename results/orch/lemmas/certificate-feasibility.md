# Certificate feasibility for L-meta-2592

Inspected locally on 2026-11-25. This is a feasibility assessment, not an UNSAT result or a Lean proof of the gap. No Lean sources were changed or built for this audit.

## Conclusion

A kernel-checked certificate can fit in the permitted one-file architecture, but there is no ready-made bridge from our current Python CNF to the existing library encoder. The checker itself is small. Whether the actual certificate fits the 512 KiB file limit is UNKNOWN until a proof is generated, trimmed, converted, and measured. Solver exit 20 alone proves nothing in Lean.

For our current generic SAT query, the shortest sound route is: retain the checked sorted normalization; define the exact custom CNF in Lean; prove that each canonical counterexample supplies a satisfying assignment; inline the existing format-compatible checker; and replay a packed RUP certificate with `decide +kernel`. Do not treat the restricted all-live/no-constant searches as complete.

## Existing encoders and their exact scope

- `lean/PEqualNP/Defs/LratEncoding.lean` (178 lines, 9,181 bytes) is already available through Defs. Its `enc`/`enc2` describe **AND, OR, and TRUE padding**, not NOT. `enc2` adds lexicographic gate ordering. `enc2CubeCount`/`enc2Cube` are cubes of this monotone encoder, not a NOT-aware encoding.
- `lean/PEqualNP/Library/LRAT/LinkN.lean` (1,277 lines, 55,210 bytes) supplies the NOT-aware model and `enc`. Operations are 0=AND, 1=OR, 2=TRUE, 3=NOT. Both source selectors of NOT are equal. A source equal to `n+j` is the false sentinel at gate j; a larger source is excluded by validity. The output may be any source at the abstract-model stage.
- Its normal form (`NF`, lines57-66) makes TRUE padding a prefix; forbids reading padding or the false sentinel outside padding; requires distinct ordered AND/OR sources; forbids NOT reading NOT; requires nonpadding gates before the last to have a later reader; and uses the last gate as output unless it is padding. Its `link` at line1249 proves completeness for **all** FanInTwo circuits of size at most s, using its own normalization.
- `lean/PEqualNP/Library/LRAT/LinkN2.lean` (597 lines, 26,646 bytes) adds lexicographic ordering of `(s1,s2,op)` except for direct dependencies/padding. `link2` (line570) and `lower_of_unsat2` (line581) link arbitrary FanInTwo circuits to its `enc2`.
- These library links do **not** retain a hypothesis that some NOT exists, and expose no exact NOT-count-preservation guarantee. Their encoder has no built-in 1–4 NOT bound. One cannot append our NOT-count or existence clauses to its formula and invoke `link2` unchanged.
- Both links accept any finite list of rows below `2^n`. An UNSAT certificate on a subset of rows is enough, provided the assignment bridge proves every full counterexample satisfies those rows.

## Mismatch with the current custom SAT formula

`results/orch/lemmas/counterexample_sat.py` allocates two exactly-one source-selector vectors of length `11+j`, followed by Boolean NOT/OR flags. The 10 true inputs are followed by fixed false at wire10. NOT reads its first source and sets the unused second selector to wire0. Binary sources satisfy `a<=b`; equal inputs are allowed. Every row allocates source values and a gate value; the output is the last gate. It asserts at least one NOT. The one/four-NOT drivers append cardinality clauses and force the OR flag false at NOT gates.

This is not the library CNF: numbering, operation selectors, padding, false representation, source equality, output clauses, and symmetry constraints differ. The generic variant is now covered semantically by `petersenSorted19FewNot`; the Python allocation/clauses themselves still need a Lean definition and satisfying-assignment lemma. A direct kernel check of an externally supplied DIMACS list would establish only that list's unsatisfiability, unless the exact list is also connected to the intended encoder.

A custom bridge should assign selectors from canonical gate inputs, NOT/OR flags from gate operations, and row variables from prefix circuit evaluation. Its clauses then split into exactly-one selectors, source mux equivalences, gate truth tables, ordering/dummy-source rules, output correctness, and NOT-cardinality constraints. Prove every allocated variable index is disjoint/in range. A generic 1–4 NOT query needs the numeric count result; an exact-one query alone covers only one case.

## Certificate checker and conversion

`lean/PEqualNP/Library/LRAT/Checker.lean` is 578 lines / 26,553 bytes. It proves `check_sound`, `checkW_sound`, and segmented `checkFirst_sound` / `checkSeg_sound` / `checkLast_sound`. It supports **RUP additions**, not arbitrary DRAT/RAT additions.

Literal representation is `2*v` for positive variable v and `2*v+1` for negative. Encoding variable0 is avoided because literal0 separates a clause from its hints. A proof step is a new store key, its clause literals, zero, then clause-hint keys interleaved with each explicitly claimed unit literal; the final hint is a conflict clause. There is no trailing hint-zero token as in ordinary textual LRAT. Initial formula keys are supplied separately by `fk`: entry0 omits that formula clause; entry `q>0` stores it under key `q-1`. Hint/new-clause keys themselves are raw keys. The checker verifies each supplied unit/conflict; bad conversion can only reject.

Thus standard signed DIMACS/text LRAT must be converted: remap literals and clause IDs; replay positive RUP hints to calculate the unit literal; discard deletion commands safely or perform consistent key management; retain the conflict hint; reject/handle any RAT steps rather than silently treating them as RUP. Standard LRAT's negative-hint RAT subproofs are not directly supported.

Packed checking stores at most1024 W-bit token fields per natural-number word, lowest first, with a high sentinel bit1. Numeric hex literals are permitted; strings are unnecessary. `checkW_sound F fk W words (by decide +kernel)` yields `not FormulaSat F`. Segments can limit kernel memory, but all segment data still count toward the single-file size cap.

The current SAT scripts provide no proof-output filename. Installed CaDiCaL help confirms usage `cadical [options] input proof`, direct `--lrat=bool`, and `--binary=bool` (default true). A future exact-instance rerun can request `--lrat --no-binary input.cnf output.lrat`; preserve the same CNF and solver options/seed and inspect the actual proof format. Whether its emitted additions are all RUP remains to be checked. Full help is saved at `/tmp/oec/pequalnp-pilot-96/cadical-cert-help.stdout` and `.stderr`. No certificate has been produced or validated in this audit.

## Inlining under the file rules

Blindly copying the library is unsuitable: Checker declares its own Trie; LinkN declares Model/Valid/NF structures and a top-level instance; LinkN/LinkN2 use local tactic macros and forbidden quoted comments. CONTRIBUTING says custom data types/instances require manual review and disallows macros/quotes.

A concrete compatible precedent is `lean/PEqualNP/Outside/L_meta_5531.lean`: its lines124–587 inline the checker using `abbrev Trie := BinaryTree (Option Nat)`, with no new datatype. That exact block is **19,240 bytes**. BinaryTree comes from `Mathlib.Data.Tree.Basic`. The same file rewrites the monotone Link model as products/conjunctions, expands the local tactics, and uses `checkW_sound` with `decide +kernel`. This gives a reusable template, although it is not the NOT-aware link.

Other examples: `L_meta_2229.lean` has a packed certificate but imports Checker/Link, which our gap does not permit. `L_meta_6111.lean` uses only Defs and proves a tiny single-RUP replay locally; it is a useful soundness example, not a scalable general solver bridge.

Measured budget: current frozen sorted helper is188,910 bytes. Adding the adapted19,240-byte checker leaves **316,138 bytes** of the524,288-byte cap for the custom encoder, assignment bridge, certificate/key data, and final statement. This arithmetic is exact; the sizes of those unwritten components and future certificate are unknown. A library-encoder route could omit our normalization and binary-floor copy, but would require solving that different unrestricted encoder and adapting its link code. The source size of LinkN+LinkN2+adapted checker is101,096 bytes before namespace/type/tactic adaptation and the few needed Shannon wire-prefix lemmas.

No final feasibility guarantee should be made until the actual trimmed certificate and complete named-file kernel build pass. Preserve any UNSAT proof files immediately; disk capacity is separately constrained.

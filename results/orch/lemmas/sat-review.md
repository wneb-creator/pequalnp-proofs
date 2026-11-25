# Independent Fano SAT encoding review

Reviewed fano_sat.py SHA256 be2deb3b190d2bb9bdda8636fb191a64fd6f3c2b8731b4b54048c20bc5f94c1d. No encoder edits.

The encoding correctly uses one-hot operand selection, earlier wires, commutative operand ordering (equal operands allowed by IsAO2), AND/OR truth recurrences, root falsity on every maximal independent set, and exact read-1 singleton/pair recurrences. Because AO2 gates have no constants or empty proof trees, an AND cannot have a one-leaf read-1 derivation; its two-leaf derivations are exactly cross products of distinct singleton derivations. Root BelowF rules out singleton derivations, so a false pair-read variable at an accepted edge means ReadTwiceAt.

The root is forced AND, accepts a repeated edge, and at least one operand is true on a maximal independent set, ensuring not both operands are implicant. Every nonroot gate is used later, so every gate reaches the last root and the root is the only maximal core.

The residual-cover constraints give a genuine vertex cover Y of G-D. The cardinal constraint is q+(14-|Y|)>=k+9, equivalent to q+7>k+1+|Y|, the strict target violation for the Fano incidence graph with tau=7.

Support filtering permits exactly the selected syntactic input set and forces each selected input to be used. Independent enumeration found maximum possible q+7-tau(G-D) by support size0..9 equal to [0,0,1,2,4,5,7,8,10,13]. Therefore supports<=8 cannot violate the k=9 bound. Independently reconstructed336 distinct Fano automorphisms and verified five eligible size9 support orbits are disjoint with sizes56,168,168,336,84, totaling812, exactly the eligible support count. Excluding supports>=10 additionally uses the checked strict core leaf bound communicated by root.

Local CNF truth-table checks:32 gate/equivalence cases passed. Complete check output is in scratch structural/fano-encoding-review-checks.txt.

Limitations: a SAT model must be independently replayed on all2^14 truth assignments and the precise core/read-vector definitions, then formalized in Lean. The no-core option drops essential core conditions and returns candidates only. UNSAT is computational search evidence, not a Lean proof or a statement about all circuits.

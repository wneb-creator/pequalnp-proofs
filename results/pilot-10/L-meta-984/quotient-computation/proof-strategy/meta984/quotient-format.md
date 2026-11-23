# Automorphism quotient frontier records

These are finite computational certificates and generation/audit records. They are not a Lean proof or a local checker acceptance verdict. The new generator preserves the prior frozen generators and frontier records.

`frontier_quotient.cpp` compiles with `g++ -std=c++17 -O3 -Wall -Wextra`. Its arguments are graph input file, maximum state count, output prefix, and score-pool file. Every one of the 31 posted graphs returned exit zero with EXHAUSTED. Their quotient frontiers contain 27,783 states in total.

Each graph automorphism is a permutation p sending vertex v to p[v]. Automorphisms are enumerated in lexicographic permutation order, including the identity first. `row_perms[a][i]` sends paired-row source index i to its destination index under automorphism a. `row_inverse_perms` gives the inverse direction required by Lean mapBits. The same action is applied separately to both halves of the 2k-bit wire encoding.

Canonicalization sorts the wire multiset after each automorphism and takes the lexicographically least resulting sorted multiset. Ties choose the first automorphism. Wire transformations are memoized. The successor filter checks raw coverage, canonicalizes, then checks the score pool on the canonical state. It does not prune a successor using its raw score. This ordering matches the orientation-aware Lean checker and does not assume score-pool invariance.

`quotient{i}.layer{s}.jsonl` stores states with s gates remaining. The corresponding `.parents{s}.jsonl` has exactly one witness on each matching line. A witness parent index addresses the line in `.layer{s+1}.jsonl`, before any later emitter reordering. Kind 0 denotes the initial state; kind 1 an alias/noop; kind 2 duplicates the input at position a; kind 3 combines the distinct input positions a and b, with a < b. Operator 0 is AND and 1 is OR. Keep bit 0 retains input a and keep bit 1 retains input b. The auto field chooses the automorphism that maps the raw child to the saved canonical child. Positions are zero based.

`audit_quotient.py` independently enumerates the complete graph automorphism group, recomputes both row-map directions, decodes every saved parent witness, and reproduces every successor using Python unbounded integers. It checks exact closure after canonicalization and score pruning. Full graph28 and graph26 audits passed before all31 generation was reported; the all31 audit has its own complete log.

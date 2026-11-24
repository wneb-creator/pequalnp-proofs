# Final prefix OR-copy chain: proof and implementation review

Verdict: PASS. The normalization is compatible with the reviewed clean-prefix,
all-live, productive, lexicographic, distinct-description, and dominance cuts.
It requires repeated operands and only constrains gates 0 through 16.

## Constructing the normal form

Delete every prefix OR(a,a) alias, redirecting all its consumers to a. Repeat
because redirection can create another OR alias. Delete duplicate gate
descriptions by redirecting the later output to the earlier identical output,
and prune unused prefix nodes. These operations preserve all wire functions
that remain in the output computation. They can be applied to a prefix of
length less than 17 without changing the four suffix gates.

If productivity or the clean-wire dominance condition fails, replace the
offending prefix AND by its allowed OR copy and eliminate the resulting alias.
The existing normalization proofs preserve the exact graph function: dominance
uses edge-row increase and unchanged independent-input values. Recheck after
sorting the remaining noncopy prefix, since a new order can expose a dominance
comparison against an earlier wire. Every failed normalization test deletes
at least one prefix core gate. No step adds core gates, so this process terminates.
At its end there are k <= 17 live noncopy core gates, with distinct descriptions,
productive ANDs, lexicographic order, and no clean-wire dominance violation.

If k > 0, the highest core gate has no later prefix gate that can read it.
Since it is live, some tail leaf must read it. Insert 17-k OR copies immediately
after the core, with the first copy reading that highest core output and every
later copy reading the previous copy. Redirect one of that output's tail-leaf
occurrences through the last copy. The highest core gate and every new copy
remain live; all other core dependencies and all suffix functions are preserved.
If k = 17 no copies are needed. If k = 0, choose any input/constant leaf used by
the tail and create a chain of seventeen OR copies from that leaf. Thus gate 0
may copy any of the thirteen input/constant wires.

## Compatibility after padding

All core operand indices are below the highest core output index. Therefore
the first copy's maximum operand exceeds every core maximum operand; subsequent
copies have strictly increasing maximum operands. Appending the chain preserves
the complete (right, left, AND-first) lexicographic order.

The core contains no OR copies. Each new copy uses a different predecessor
wire, so no two added descriptions coincide and none equals a core description.
Hence description distinctness is preserved. Productivity restricts only ANDs;
the new gates are ORs. Every new copy is after every core AND, so it supplies no
new earlier clean wire against which an AND could fail dominance. No additional
normalization loop is needed after the final chain is inserted.

Tail leaf-order symmetries can be restored by relabeling within the reviewed
symmetric groups. This preserves each fixed formula's value; the seven-case
overapproximation imposes no suffix-junk conditions. For the unrestricted
shard circuit, adding OR copies leaves independent-input values and junk status
unchanged, and restores the suffix to positions 17 through 20.

## Exact 412-clause formulation

Write A_g for the operation bit, true for AND; L[g,a] and R[g,a] select operands.
For each g=1..16 and every a other than the immediately previous gate output
wire 13+g-1, add

    A_g OR NOT L[g,a] OR NOT R[g,a].

This forbids an OR copy from any other wire but places no restriction on ANDs
or ORs with unequal operands. There are sum(g=1..16)(12+g) = 328 such clauses.

For a potential copy at g=0..15, use the guard

    A_g OR NOT L[g,a] OR NOT R[g,a]

and append respectively NOT A_(g+1), L[g+1,13+g], and R[g+1,13+g] to obtain
three clauses. These force the next prefix gate to be an OR copy of g.
At g=0 all thirteen possible sources must be handled. At g=1..15 only the
immediately previous source remains possible under the preceding prohibition.
This contributes 3*(13+15) = 84 clauses, for 412 total and no new variables.

The propagation stops at prefix gate 16. It does not force suffix gate 17 to
be OR, and imposes no copy-chain requirement on the four tail gates.

Consequently either there are no prefix OR copies, or they form one final
contiguous chain whose first source is the immediately previous noncopy gate
(or an input/constant if it starts at zero). A local prohibition without the
forward-copy clauses would not be sufficient for this global shape.

## Reviewed implementation

add_prefix_copy_chain in search_l1342_shard17_copychain.py uses exactly these
guards, source indices, and bounds. It runs after the dominance delta and before
writing or allocating lex flags. It adds no variables; all existing variable
IDs remain unchanged. The rest of the reviewed dominance functions are unchanged.
The generated variants include both dominance and optional distinct-prefix.

The JSON companion records source and case hashes, the exact clause-sequence
audit, and a finite check of all 2^17 copy/noncopy patterns. No solver was started
and no running CNF or repository file was modified. This remains a mathematical
normalization review rather than a Lean proof or certificate verdict.

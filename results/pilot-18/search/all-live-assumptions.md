# Scope and assumptions of the self-contained generator

The companion file is `sat_mono_prefix17_standalone.py`. It uses only the Python
standard library and contains its own CNF helper, target function, and model
decoder. It does not run a solver, contact a service, or read credentials.

The graph has vertices 0 through 10 and edges

    (0,9) (0,10) (1,4) (1,8) (2,5) (2,10) (3,6) (3,7)
    (4,8) (4,10) (5,8) (5,9) (6,7) (6,10) (7,9) (8,9).

The target F is true exactly when the selected vertices contain an edge.
There are sixteen minimal positive inputs and twenty-four maximal independent
sets. For monotone circuits, correctness on these forty inputs is equivalent
to correctness on all 2048 inputs. The decoder independently checks all 2048.

## Circuit model and basic encoding

Inputs are wires 0..10. Wires 11 and 12 are free FALSE and TRUE. Gate j produces
wire 13+j; both operands are earlier wires. A positive operation variable means
AND and a negative operation variable means OR. Repeated operands are allowed.
The default output is selected from all wires, and default gates can be dead.

The free constants overapproximate the repository's model. Every original gate
with at most two inputs, including constants, unary gates, repeated operands,
and unavailable-wire reads, can be represented with the same number of gates.
A SAT solution may use free TRUE in a way requiring additional gates when
converted back; it must not be presented as an original-model witness without
conversion and gate counting. UNSAT excludes original-model witnesses.

Junk means an AND gate true on at least one independent input. It is equivalent
to truth on at least one maximal independent set. The default shard requires
the first junk at index 17 and at least one more junk gate later.

Before index 17, a wire on nonempty independent inputs is exactly the OR of its
singleton support. Inputs have singleton supports, OR takes union, and clean
AND has empty support. Free TRUE has full support. A prefix AND with operand
supports A,B is clean exactly when every a in A and b in B are distinct and
adjacent. The generator enforces all forbidden ordered pairs. Edge-input
values are computed by the actual Boolean operation rather than this abstraction.

There is no need to represent the empty input separately: zero on every maximal
independent set implies zero there by monotonicity. The pure-OR representation
of free TRUE is asserted only on nonempty independent sets.

## Prefix sorting

`--prefix-sort` requires nondecreasing maximum operand indices through the
seventeen prefix gates. Among available prefix gates, emit one with the smallest
maximum predecessor index. Newly available gates read the just-emitted wire,
whose index exceeds every previously available key. The chosen keys therefore
cannot decrease. Renumbering the prefix and updating all suffix/output references
preserves gate functions, all junk conditions, and the FIRSTJ position.

## Moving the output last

`--last-output` fixes the output at the last gate. The completeness argument here
is specific to size at most 21, FIRSTJ=17, and at least two junk ANDs. Pad shorter
circuits to 21 gates with unused OR copies before applying these cases:

* Output 20: no change.
* Output 19: keep 0..17, insert AND(17,17) at 18, move old 18 and 19 to 19 and 20,
  updating references, and discard unused old 20.
* Output 18: keep 0..17, insert the junk copy at 18, move old output 18 to 19,
  and put OR(19,19) at 20. Discard unused old 19 and 20.
* Output 17 is impossible because it is junk and F is clean.
* An earlier output: keep 0..17, put AND(17,17) at 18, then two OR copies of the
  old output at 19 and 20.

Indices in these descriptions name gate outputs, not the literal wire numbers.
The first junk remains 17; the inserted AND copy supplies a second junk. Prefix
sorting, if already imposed, is unchanged. Other parameter settings still accept
the flag as a search restriction; no shard-preservation theorem for them is claimed.

`--last-op and|or` requires `--last-output` or `--live` and partitions the search
according to the last gate's operation. Neither branch alone is complete.

## All-live normalization

`--live` implies last output and rejects parameter settings other than size 21,
FIRSTJ 17, and at least two junk ANDs. It adds one clause per gate below 20,
requiring a later reader. In a topologically ordered finite circuit with output
20, these clauses are equivalent to every gate reaching the output. Repeated
operands and semantically redundant gates remain allowed.

The normalization uses the repository theorem `PEqualNP.Outside.L_meta_1407`:
for a C4-free graph, a circuit whose AND gates are all below the edge function
has a cover T with |E|+|T| <= gates+1. This graph has no 4-cycle. Its disjoint
triangles (1,4,8), (3,6,7), and pentagon (0,9,5,2,10) force every cover to have
at least seven vertices. Thus a clean circuit for F needs at least 22 gates.
This lower bound also holds with free constants: propagate constants and delete
copies in a hypothetical clean computation; no retained AND changes its clean
function, and the nonconstant output has an original-model realization of no
greater size.

After moving output last, some junk AND must reach the output. Otherwise prune
the output dependency graph to obtain a forbidden clean circuit. If gate 17 is
dead, the first live junk is gate 18 or 19. For 18 its operands are prefix wires.
For 19 at least one operand is a prefix wire unless both operands are 18. In
that exceptional case, 19 is a copy of dirty OR gate 18; deleting this copy and
dead 17 again gives a forbidden clean circuit. Choose a dirty prefix operand b,
replace dead 17 by AND(b,b), and redirect that operand of the live junk to 17.
Output behavior is unchanged, and 17 is now live and junk, with a later junk.

Fill dead suffix gates as follows:

* If 18 and 19 are dead, insert the chain 17 -> 18 -> 19 -> 20 of AND copies.
* If only 18 is dead, copy 17 there and redirect a later live use of 17 to 18.
* If only 19 is dead and 18 reads 17, move old 18 to 19, copy 17 at 18, redirect
  its read in new 19 through 18, and update output references from old 18 to 19.
* If only 19 is dead and 18 does not read 17, both 17 and 18 must directly feed
  20. Copy 17 at 19 and redirect its output use through 19.

These AND copies are junk and preserve all functions used by the output. Now
delete unused prefix nodes and renumber the k remaining prefix nodes. Insert
17-k OR copies on a live prefix-to-suffix edge, redirecting that edge through
the copy chain. All inserted prefix nodes are live ORs, so the first junk stays
17. The suffix functions and second junk are preserved. Prefix sorting may then
be applied as above.

For a direct proof on raw Lean gates, nullary junk ANDs require a separate case:
make 17 nullary TRUE and change the useful nullary AND to AND(17,17). Prefix
padding can use any live prefix-to-suffix edge, avoiding an assumption that
nullary 17 has an operand. The binary augmented encoding already has free TRUE
as an operand and needs no separate implementation case.

## What is and is not implemented

The script adds exactly the requested optional last-output, last-operation, and
liveness clauses. It does not silently add the clean-tail cuts, a restriction
on total AND count, semantic irredundancy, or distinct-operand restrictions.
The mathematical normalizations have independent review; they are not yet Lean
proofs in this script. An UNSAT solver result would still need the intended
certificate and translation checks for a posted theorem.

Metadata records `program_sha256` for the generator's own source and `sha256`
for DIMACS. With `--prefix-sort` and none of the new flags, the CNF is byte-for-byte
the original sorted file: 3957 variables, 71560 clauses, SHA-256
`2139e0f2b731ed921526c475a76553339be72dff1d14d2fae1a09a80cf9341c1`.
The unsorted default likewise matches the original unsorted file exactly.

Validation checked both byte identities, eight rejected option combinations,
1002 liveness patterns against independent backward reachability, fixed correct
graph circuits under both root-operation flags, the embedded decoder on 2048
inputs, and execution after relocation under isolated Python. The original
running CNFs and generator were not changed, and no solver was started.

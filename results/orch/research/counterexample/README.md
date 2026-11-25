# L-meta-2583 counterexample search

This directory contains finite searches for an AND/OR circuit with at most 26
gates for the Fano incidence function on 14 inputs. A successful witness would
contradict the proposed read-1 normalization, because the read-1 minimum is 27.
No witness has been found so far. Timeouts and local-search failures are not
lower bounds.

The graph has point inputs 0 through 6 and line inputs 7 through 13. Point p is
incident with line l exactly when (p-l) modulo 7 belongs to {0,1,3}.

`generate.py` constructs all 21 minimal true assignments and all 37 maximal
false assignments. It exhaustively verifies that every true assignment extends
one of the former and every false assignment is contained in one of the latter.
For a monotone AND/OR circuit, agreement on these 58 assignments is equivalent
to agreement on all 16,384 inputs. The script also verifies the canonical
27-gate star circuit on the full truth table and writes `problem.txt`.

`search.cpp`, `search-v2.cpp`, and `search-v3.cpp` are stochastic circuit
searches. The first uses star-circuit seeds. The second adds dual stars,
randomized OR trees, semantic-neutral gate exchanges, asymmetric penalties,
and a pool of near-solutions. The third adds 28-gate nonlinear seeds based on
the identity

    a(b OR C) OR d(b OR E)
      = (a OR d) AND (b OR aC OR dE),

and its three-collinear-center generalization, then deletes two gates. Every
nonlinear seed is checked on all 58 characterizing assignments; the saved
`nonlinear-28-seed.txt` is independently checked on the full truth table.
Each run is capped at 300 seconds. Programs, complete logs, and an independent
full-truth-table validator are preserved.

`synthesize.py` is an exact bitvector-multiplexer encoding in Z3 5.3.3. Every
gate selects two earlier wires and AND or OR. It permits repeated operands,
orders operands by commutativity, places the output last, and requires every
nonfinal gate output to be read later. These conditions preserve existence for
at most the requested number of gates: remove unused gates and pad the output
with repeated-operand OR gates. The fixed canonical 27-gate sanity check is
SAT and passes all 16,384 inputs. The unrestricted 26-gate run timed out after
900 seconds with verdict UNKNOWN.

`synthesize-pruned.py` adds optional balanced multiplexers and normal-form
restrictions. Useful-gate restrictions require every gate to be true on some
minimal positive and false on some maximal negative. A minimum-size witness
can be chosen this way by constant substitution and propagation. Top-form
restrictions forbid AND operands below the target function and mixed OR gates
with exactly one operand below it. Selecting a minimum circuit with the fewest
dirty OR gates justifies the latter via size-preserving implicant lifting.
Below the target means zero on all 37 maximal-negative assignments.

The optional fixed-bad-edge mode tracks the three square-free monomials x, y,
xy at every wire for edge (0,7), and requires xy to be absent at the output.
The read-1 lower bound and edge transitivity justify searching this mode.
It cannot be combined independently with unrestricted first-gate orbit
normalization; the script rejects that combination.

`automorphisms.py` verifies 168 point-line automorphisms and their 168 duals,
and checks that all 91 unordered distinct input pairs form three orbits with
representatives (0,1), (0,7), (0,9), of sizes 42, 21, 28. Together with AND/OR
this gives six first-gate cases. Useful-gate pruning removes the two cases
where gate zero is an AND on a nonedge, leaving four cases. This concerns gate
zero, not the first AND appearing after arbitrary OR preprocessing.

All solver input files, complete stdout/stderr, and returned models are saved.
A SAT model is independently checked on all 16,384 assignments before being
reported as a circuit witness. No result here substitutes for Lean checking.

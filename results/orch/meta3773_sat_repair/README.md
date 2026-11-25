# Five-point repair and warm-phase SAT diagnostics

These are incomplete search diagnostics for L-meta-3773. No 63-gate circuit,
global refutation, or new Lean proof is claimed.

The seed has 21 local gates, preserves all 20 positive edges, and is wrong on
15 of 30 maximal negative cuts (309 of the 65,536 physical assignments).
Padding with edge AND(0,12) and a final OR produces 23 gates without changing
its physical truth table. The colex reordering was also checked exhaustively.
The local SAT searches retain all compatible outside OR-tree choices as free
variables, require all gates active and positive somewhere, and require an
AND that fires on a negative cut. Raw leaf and helper-count constraints remain.

Cold repair round 0 reports UNSAT in 25.97 seconds for at most five gate
changes relative to that normalized seed. This is only a restricted finite
neighborhood exclusion, not a global lower bound. Its exact CNF, inputs,
metadata, frozen generator and full solver output are preserved. No checked
SAT proof certificate was generated. Cold round 1 allows eight changes and
is inconclusive after 110 seconds.

The warm-phase wrapper performs only a bijective variable-polarity renaming
of that same eight-change CNF, making the default false phase correspond to
the seed selectors, operations and test values. It checks the renaming is an
involution clause by clause, binds both DIMACS hashes, undoes the polarity
changes before model decoding, checks every original clause, and verifies any
decoded circuit on all 65,536 physical assignments.

The 24-gate positive control passes every original and renamed clause, returns
SAT in 0.066 seconds, and passes full physical verification. This control has
24 local gates and is not a solution of the requested 23-gate patch. Warm
production results are recorded in their status and full solver log; absent
a zero-error 23-gate candidate file they provide no witness.

The source seed uses 0=AND,1=OR. The normalized SAT circuit uses 1=AND,0=OR.
The strict conversion, integer fanin guards, decoded mutation count, original
clause replay and exhaustive physical checks protect this interface.

All source/data/CNF inputs are hash-bound. Child solvers use only an ordinary
environment, disable core dumps and impose CPU, address-space and wall caps.
The exact original and transformed DIMACS files are compressed losslessly;
the manifest binds both compressed and uncompressed hashes and lengths.

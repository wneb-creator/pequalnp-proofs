# Native pair-selection control

Before the new full-star run, the unchanged reviewed native engine was tested
with `--pairs 32 --threads 2` on the independently reviewed nine-variable
star-support equations. This smaller system was already known to have a unit
basis from separate exact QQ and finite-field computations.

An independent input parser reconstructed every polynomial modulo 1009 from
the sparse input and checked it against the corresponding primitive-scaled
source polynomial. All scaling factors are invertible modulo 1009.

The native control returned exactly `[1]` over F1009 in 0.034 seconds, exit 0.
It completed fifteen pair-processing rounds and the final basis reduction.
Several rounds selected 32 or 33 pairs, so the batching path was exercised.
The upstream implementation can include additional pairs with a shared least
common multiple at the selection boundary; the parameter is 32, not a strict
upper bound on every reported selection count.

The frozen ten-file `native-b32-control/` archive contains the reviewed source
equations, exact input/provenance, roundtrip checker, complete logs, outcome,
and single-polynomial basis. This is a control for the changed solver setting;
it is not a result for the full eighteen-variable chart or the posted gap.

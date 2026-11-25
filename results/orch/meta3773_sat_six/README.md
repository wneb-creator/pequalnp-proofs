# Six-point SAT diagnostics

This is a parameter adaptation of the independently reviewed five-point SAT
encoder. It uses 19 raw inputs, 21 compatible outside OR signals, 28 local
gates and all 83 extremal rows (24 positives and 59 maximal negatives).
Each of seven outside groups has 15 tree variants. The production query fixes
exactly seven AND gates and requires all gates active and positive somewhere,
with an AND that fires on a negative cut. It is a restricted diagnostic query.
No global lower bound or new Lean proof is claimed.

The ordinary six-star positive control has 29 local gates. Its complete
408,893-clause encoding was checked under the explicit assignment, and its
physical function was independently verified on all 524,288 inputs. The
control is not a solution of the requested 28-gate patch.

Any production SAT candidate must pass the independent exhaustive physical
replay and then be assembled and checked on the original 26-input instance,
including the prescribed first gate. A status without a verified 28-gate
candidate is not a witness. Full source, model data, metadata, status and
solver logs are preserved; the exact production CNF is losslessly compressed.

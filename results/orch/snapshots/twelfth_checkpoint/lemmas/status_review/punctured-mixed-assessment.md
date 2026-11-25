Mixed point/line outside decomposition assessment, 2026-11-25

The finite generator `prepare_punctured_mixed.py` derives both packets from the
posted 52-edge predicate. It checks the exact edge partition, regenerates the
complete maximal-negative family, and exhibits a pivotal pair for every raw
coordinate while every available OR feature stays fixed. These are computational
certificates and mathematical search accounting, not Lean lower-bound theorems.

For owners 0, 1, 3, puncturing their common line 13 leaves nine edges on twelve
raw inputs. Ten outside point stars cost 49 gates; the partial line star costs
three, and joining those outside pieces costs one. A final OR leaves a target
of nine paid core gates. All twelve raw coordinates remain pivotal even when all
forty candidate OR features are supplied simultaneously. A fan-in-two output
cone reading twelve distinct raw sources requires at least eleven gates.
Consequently this nine-gate construction profile is impossible.

For owners 0, 1, 2, 6, puncturing their two incidences on line 13 leaves fourteen
edges on thirteen raw inputs. Nine outside point stars cost 44 gates; the partial
line star uses point0 OR point1 and one AND, costing two; joining outside pieces
costs one. Outside cost is 47, so a core of at most fifteen gates plus the final
OR would give a full circuit of at most 63 gates. The packet exposes 24 OR
features: five fixed triples, fifteen optional pairs in five compatibility
groups, three fixed line pairs, and the fixed point pair. At most one optional
pair per group is available at this zero-extra outside cost.

The second packet has sixteen maximal negatives. Every raw coordinate has an
explicit pivotal witness holding all 24 features fixed. Thus any fifteen-gate
core can use at most three distinct feature inputs, because its output cone has
at most sixteen distinct external sources. If it uses three, that cone must be
a read-once tree over the thirteen raw and three feature sources. This is a
necessary support constraint, not an existence claim.

The four-owner construction is a focused subclass of the previous eighteen-gate
full-four-owner problem: restoring the punctured line inside that earlier core
costs a point OR, an AND, and an OR. It is a distinct sharing/decomposition
profile, not a larger circuit class. The raw star core baseline here costs
seventeen gates, so the target requires a two-gate improvement. No target core
or assembled witness is known. The compatible outside assembler requires an
independent audit before any solver result can be called a full witness.

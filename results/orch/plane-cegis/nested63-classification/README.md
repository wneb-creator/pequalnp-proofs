# Incomplete nested63 warm circuit classification

This independently replayed circuit has63 gates,16 ANDs, and exactly two dirty AND wires28 and31. No AND is true on a singleton input. It misses six of52 positive rows and accepts none of704 maximal-false rows; it is not a solution to the gap. All26 singleton rows were checked too. The compact model and literal circuit agree on all782 tested rows.

The original classification came from not_elimination; gate_elimination regenerated the complete boundary from the sum-incidence geometry and independently replayed the literal and compact representations. The first audit run completed its semantic assertions but failed while writing metadata because a loop index shadowed a path variable. The final script fixes that variable name; audit2 exits0. Both complete logs are retained.

This record is a finite diagnostic and was not substituted into the running full query.

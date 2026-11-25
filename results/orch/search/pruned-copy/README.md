Pruned first-copy certificate fixture and bounded monotone search

The 61,729-byte JSON fixture starts from archived monotone state 0 at budget 12.
It contains 14 explicit labelled basis nodes, 269 retained entries, 40 subtree
cofactor cuts, and 2 copied-basis bridge cuts. All lower bounds in this fixture
are 15 after fixing one input to zero. The copied basis keeps original labels
and appends two distinct labels with equal raw values. Every closure table
contains all active singleton leaves. Cut witnesses preserve full supply
histories and selected history indices. This is finite experimental data; it
has not yet been instantiated in the unified Lean certificate checker.

The C++ sources compare the earlier compact-cache prototype with lazy
restriction caches and cofactor pruning before symmetry canonicalization.
The latter also removes redundant per-parent canonicalization; recursive
memoization still compares the exact root multiset and remaining budget.
The memory guard is an estimate, not a hard process-memory cap.

Command: ./copy_search_pruned_lazy --cap 19 --seconds 60 --nodes 1000000
Result: unfinished at 60.0075 seconds, 41,908 recursive visits, 4,896 closures,
151,884 retained entries across closed tables, and 1,560,075 subtree cuts.
The run did not prove the monotone 19-gate root case. Its log is complete.

The general certificate proof and individual forest/compression lemmas are
being developed separately. Neither this incomplete root search nor its
recurrence is claimed here as a checked proof of the posted statement.
The exporter currently uses original scratch paths for its dependencies.

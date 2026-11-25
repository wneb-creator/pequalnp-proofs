# Formula-only finite checks for L-meta-3754

The exact truth-table dynamic program enumerates nonredundant AND/OR formulas over five or six inputs, keeping the minimum formula size for each (function, has-dirty-AND) state. At every OR, it rejects the lift configuration: one operand implies the final graph function, while the OR does not. All wires are satisfiable in this constant-free model and all formula gates are in the output cone, so this is the fixedpoint condition for formulas. Semantically redundant gates are omitted; such a formula cannot be minimum.

All 9 nonempty unlabeled forests on five vertices and all 19 on six vertices were covered, including isolated vertices. No dirty fixedpoint formula occurs at size at most |E| + minimum-vertex-cover-size - 1. Clean formulas attain that bound in every case. A positive control on the four-vertex path with one isolated variable finds a dirty fixedpoint formula at size 5, while its clean minimum is 4.

This is computational evidence about formulas only, not a Lean proof, not a search of circuits with shared gates, and not a proof of the posted statement. The six-variable script reads the preceding five-variable graph representatives; change its absolute input path if rerunning elsewhere. Full stdout and stderr are preserved in the corresponding logs.

# Completed Triangle9 run005

The reviewed Triangle9 search ran for1200.044539seconds with seed14772916, completing43,184,128mutations and2400epochs with330matching warm starts. Its best valid circuit remained53gates; the target52was not found. The complete log, two best-valid fixtures, and numeric frontier are preserved. A frontier entry with a positive error count is not a valid circuit. This heuristic run establishes no lower bound.

Source and exact finite test data are preserved in sibling `triangle9-search/`. Both concrete valid fixtures were decoded and scalar-checked on all557raw extremal cases by the reviewed recorder; they still require a Lean certificate for formal use. The standard53gate baseline has already been checked separately in the Lean artifacts. No invalid near circuits were recorded by this source version; the next reviewed `triangle9-near/` source adds those repair seeds.

# Optional first-AND anchor for a future free-OR query

This is a reviewed mathematical normalization, not an implemented constraint in the active global-disjoint12 query. It applies to the unrestricted OR-subset model with all52 positive edge rows and all704 negative boundary rows. It does not establish completeness for a fixed prefix or a bounded-membership-cost model.

After making the two operand source subsets of each AND disjoint, replace every AND whose value is false on all52 positive rows by false. On those positive rows, every later wire retains its original value. On negative rows, every later wire can only decrease, since the network is monotone. Thus correctness is preserved. Drop the false source memberships, remove the deleted AND records, renumber the survivors, and pad empty false records at the end to restore the slot count. Dropping memberships preserves disjointness. At least one AND survives because the target has positive inputs.

The first surviving AND has only primary sources and accepts some incident point-line pair. Its disjoint operand subsets therefore contain the two endpoints on opposite sides. A projective-plane automorphism maps that incident pair to point0 and line0 (input13). Swapping that AND's operands if necessary gives the anchor that its left subset contains input0 and its right subset contains input13.

The source-subset representation charges no OR cost, and empty operand subsets remain legal. The active12-AND warm point-star model already satisfies these two membership choices, but no anchor units have been added to that frozen query. The argument was independently approved by proof_route and circuit_search on2026-11-25. A future implementation still requires a precise source-delta/control audit before launch.

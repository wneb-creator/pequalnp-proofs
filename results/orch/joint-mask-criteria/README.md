# Additional bounded two-product criteria

This extends the reviewed JointUnion diagnostic with two explicit criteria, on six eight-vertex bipartite C4-free hosts: theta(3,3,3), C8, P8, C6 with two leaves, the overlap-budget tree, and a four-edge matching. Each product has disjoint operands of size at least two and is dirty. Both searches require an accepted joint host edge.

The forest criterion retains full joint cleanliness and checks the contributed edge union U with a union-find cycle test. All six censuses found no cycle. The budget_one criterion weakens joint cleanliness to two-element assignments only and checks |U|>K+1, where K is the explicit shared-quadrant OR cost from the original diagnostic. No violation was found. Equivalently, the tested inequality is |U|≤N+r−3. These are finite diagnostics, not general theorems or posted-gap results.

The source retains the original unused edge-budget switch for compatibility; `--criterion` controls the actual predicate. Reproduce with `python3 SearchJointCriteria.py --output result.json --vertices 8 --disjoint-min-two --criterion forest --seconds 20` or with `--criterion budget_one --pair-only`.

Each host tests all 2,073,666 unordered pairs of 2,037 distinct products. Logs and JSON are complete; no run timed out. All effective-mask tests retain full truth-table cleanliness, including in the pair-only joint variant.

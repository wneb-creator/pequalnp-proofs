# Triangle9 archive diversity and shared-sum warm starts

This extends the reviewed near-recording search with active physical AND count in the archive key. It preserves states with additional interacting helpers even when their output signature matches a cheaper clean-star state. The archive still has the same10000-entry bound. Mutation, objective, evaluator, costing, and valid/INVALID recording remain unchanged.

A new warm-start branch shares s=a∨b across g1=s∧N(a), g2=s∧N(b), and uses a∧g1 and b∧g2 as the corresponding stars. It activates only a dormant prefix OR and two dormant AND rows that precede every rewritten star. The function remains exactly the Triangle9 target; cost is56, three above baseline53. The preserved fixture has exactly two dirty AND gates. These are search starts, not target52 witnesses. Existing interacting matching starts at59 remain available.

Author calibration checked768 full valid baselines on557raw extremal inputs and2304 baseline/mutant physical expansions, including85 shared-sum starts. Independent review checked96 full-grid baselines on557cases, including13 shared-sum starts, and exact topology/count. All logs are complete. The reviewed source SHA is915d0cd5cb8e98d341179b0253920c1302f73b13848fc3829e98634393c00438.

Planned same-slot command: `python3 SearchStochasticTriangle9Diverse.py --seed 14772921 --seconds 1200 --output-dir <scratch-directory>`. No run result is claimed in this package.

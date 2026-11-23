UNVERIFIED native exclusion candidates for L-meta-670

These C++ computations are not a Lean proof and do not establish the posted theorem until the independent Lean finite checks pass. All data is public Boolean graph data. No credentials are present.

The graph has 9 inputs and edges (0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5). The diagnostic signature contains 414 positive/negative assignment pairs. Twelve projection oracles are used: three 8-input circuit lower bounds of 13, and nine 7-input theta circuit lower bounds of 11. Their applicability and the finite search still require Lean checking.

Build the standalone C++17 source:
  g++ -O3 -std=c++17 live_theta12.cpp -o live_theta12 > compile.stdout 2> compile.stderr

Run each exact NOT-count case t=0,...,7:
  ./live_theta12 1200 100000000 15 0 > t0.stdout 2> t0.stderr
Replace the final argument by each integer 1 through 7. Arguments are seconds, node cap, gate budget, exact NOT count. The engine samples the time, node, and 4GB reported-peak-RSS caps every 65,536 calls; caps can be overshot between samples. An EXCLUDED result means the search completed without a sampled stop condition, not that instantaneous resource use always remained below every cap. UNKNOWN is not an exclusion. Hash table keys are compared exactly. Graph symmetry is used only to memoize excluded states, never to claim a hash collision is equality.

The saved theta15t0.out through theta15t7.out each report EXCLUDED. Their full stdout and stderr are included. Calls by t: 1159421,935371,386158,180803,46201,13565,955,478.

To regenerate a cut-13 frontier, compile live_theta_frontier.cpp likewise and run:
  ./live_theta_frontier 60 10000000 15 0 13 ThetaFrontier13t0.json > export.stdout 2> export.stderr
Replace t as above. Records contain exact 414-bit wire signatures, 4-bit postfix expression recipes, and twelve projected prefix programs (old inputs0..7,false8,true9,gate outputs10+j). Record kinds:0=recursive leaf,1=projection prefix exclusion,2=top branch. All recorded programs and signature recipes have been independently replayed in Python; see theta-frontier-validation.out.

The eight frontier JSON files are stored with gzip compression. After decompression into this directory, python3 validate_theta_frontiers.py repeats the independent validation. Domains12.json gives exact selector maps, input orders, and lower-bound numbers; Data414.json describes the original diagnostic pairs and graph symmetries.

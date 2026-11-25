Paused after root reported leaseHTTP410. No search process remains active. No63-gate proof was found.

Completed runs:
-64-gate control: all756tests correct;45.781s and336105iterations.
-70-gate control: all756tests correct;1.38707s and6053iterations.
-Fixed-penultimate-tap61 search:900s,2009restarts,6,025,471iterations; best1wrong test. This restricts tap placement and is not evidence against arbitrary auxiliary wires.
-Semantic-preserving slack:900s and11,374,701iterations; minimum64active gates.
-Adaptive63 search:1200s and11,043,091iterations; best1wrong originaltest. Proper-dirty candidate still misses9positive edges. Sampled error locations cover all52positives and704negatives over the run, not every iteration.

Interrupted runs:
-Point-superset search: last complete restart127 /3,810,000iterations /663.911s; best197maximal-negative errors, still a trivial singleton false-positive basin. All52positive edges remain correct.
-Pair-priority completion-seed search: last complete restart24 /720,000iterations /138.506s. Best candidate has63gates, all52positive edges and26singleton negatives correct,2false nonedge pairs, and140false maximal-independent tests. This is partial evidence only and is not a proof. Full logs and candidate JSONs are under runs/pair-priority/.

Prepared but never run: search-tap-free.cpp (25inputs,61gates; arbitrarytap among86wires), search-superset-bank.cpp (26inputs,63gates,782tests), and search-grid-superset.cpp (17inputs,28gates). The free-tap source has a documented minor missed-solution risk at a final unchecked perturbation; no false-witness risk was found. Do not resume work until root confirms a new live lease.

All counts are computational unless explicitly described as independently audited. No file here claims the posted63-gate theorem.

Frozen atUTC: 2026-11-25T15:26:34.530239+00:00

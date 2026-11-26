# Bounded Lean thread experiment

Four independent lemmas each check four frozen packed nodes: 4992–4995,
4996–4999, 5000–5003, and 5004–5007. The module imports only `PackedDirect`;
it does not import any previously proved range module. Every lemma uses
`decide +kernel`.

Two fresh processes checked the identical source in order, with `-j1` then
`-j4`, both using `-M7500 --profile`. No `.olean` was emitted. Both exited 0.

| Threads | Wall seconds | User seconds | System seconds | Peak RSS KiB |
|---|---:|---:|---:|---:|
| 1 | 19.5488 | 18.0417 | 1.1994 | 3,645,768 |
| 4 | 19.8002 | 18.2786 | 1.3235 | 3,651,120 |

There is no observed speedup. CPU time divided by wall time is approximately
one CPU equivalent in both runs. The four kernel-check profile times sum to
17.4 seconds for `-j1` and 17.6 seconds for `-j4`. This one pair does not
establish anything about other modules or parallelization strategies.

The cgroup allowed four CPU equivalents and 16 GiB. Imported files were
already cached. Earlier proof workers ended before either measured launch;
the launch receipts show only zero-RSS zombie entries. Neither run changed
the memory-event counters or triggered the driver's conservative memory stop.
Completion polling every 0.25 seconds adds up to one polling interval to wall
time, making the small observed difference unsuitable for a slowdown claim.

`j1.stdout`, `j1.stderr`, `j4.stdout`, and `j4.stderr` retain the complete Lean
streams. Each run has exact `wait4` user/system/peak-RSS metrics and sampled
cgroup memory. Driver streams and installed Lean help are also retained.
`summary.json` records the exact commands and source hashes.

The job-specific launcher supplies the frozen module/library search path.
To repeat in the same prepared job environment, run `run_one.py --threads 1`
and then `run_one.py --threads 4` in fresh processes. Repeating overwrites
measurements and changes this package's hashes. No production source changed.

These are finite Python checks supporting plausibility of the two reduction children. They do not prove either child.

Run scripts from this directory so local imports resolve.

- `python3 split.py`: exhaustive semantic circuits through four gates on the four recorded graphs.
- `python3 random_split.py`: random Fano-incidence subgraph checks.
- `python3 target1006.py`: targeted analysis of the nearby vertex-cover refutation.
- `python3 hall.py`: matching-resource condition.
- `python3 weak_soundness.py`: singleton/pair-only soundness experiment.
- `free_and_three.log` records explicit calls to `run` with `max_or=3`, whereas `free_and.py` defaults to 2 in its script entry point; use the graph tuples recorded in the log.
- `python3 free_and_last.py`: remaining C6 final-OR cases.

Complete stdout/stderr diagnostics are preserved in the corresponding log files.
